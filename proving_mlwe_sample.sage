# This is the script for computing the non-interactive proof size
# of proving knowledge of a MLWE sample described in Section 7.1.
# Concretely, we want to prove knowledge of a vector s such that
# norm of ||(s,As-u)|| is at most B.

# Function for estimating the MSIS hardness given parameters:
# a (n x m) matrix in \Rq along with the solution bound B. It returns the
# root Hermite factor \delta. We use the methodology presented by
# [GamNgu08, Mic08] and hence m is irrelevant.

def findMSISdelta(B, n, d, logq):
	logC = log(B, 2)		
	logdelta = logC^2 / (4*n*d*logq)
	return 2^logdelta

# Function for estimating the MLWE hardness for a (m x n) matrix in \Rq and 
# secret coefficients sampled uniformly at random between -nu and nu.
# We use the LWE-Estimator by [AlbPlaSco15] as a black-box.

def findMLWEdelta(nu, n, d, logq):
    load("https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py")
    n = n * d
    q = 2^32
    stddev = sqrt(((2*nu+1)^2 - 1)/12)
    alpha = alphaf(sigmaf(stddev),q)
    set_verbose(1)
    L = estimate_lwe(n, alpha, q, reduction_cost_model=BKZ.enum)
    delta_enum1 = L['usvp']['delta_0'] 
    delta_enum2 = L['dec']['delta_0']  
    delta_enum3 = L['dual']['delta_0']  
    L = estimate_lwe(n, alpha, q, reduction_cost_model=BKZ.sieve)
    delta_sieve1 = L['usvp']['delta_0'] 
    delta_sieve2 = L['dec']['delta_0']  
    delta_sieve3 = L['dual']['delta_0']
    return max(delta_enum1,delta_enum2,delta_enum3,delta_sieve1,delta_sieve2,delta_sieve3)

# Security parameter, ring dimension of \R and challenge space
kappa = 128                             # security parameter
d = 64                                  # dimension of R = Z[X]/(X^d + 1)
l = 2                                   # number of irreducible factors of X^d + 1 modulo each q_i, we assume each q_i = 2l+1 (mod 4l)
omega = ceil( (2^(2*kappa/d) -1) / 2 )  # maximum coefficient of a challenge. We want |\chal| = (2*omega+1)^(d/2) >= 2^kappa
C1 = 158                                # the heuristic bound on \sqrt(|| \sigma_{-1}(c)*c ||_1) 

# Defining the log of the proof system modulus -- finding true values will come later 
eta = 1                                 # number of prime divisors of q, usually 1 or 2
logq1 = 32                              # log of the smallest prime divisor of q
logq = 32                               # log of the proof system modulus q
lmbda = 2 * ceil( kappa/(2*logq) )     # number of repetitions for boosting soundness, we assume lambda is even

# Length and size of the committed messages
m1 = 16                                # length of s1
ell = 0                                # length of m 
alpha = sqrt(1024)                     # norm of s1

# Parameters for proving norm bounds
Z = 1                                  # number of exact norm proofs 
BoundsToProve = [sqrt(2048)]           # define Z bounds B_1,...,B_Z
B_sum = 0
for i in BoundsToProve:
    B_sum += i^2                                  
B_sum = sqrt(B_sum)                    # quadratic mean of the bounds B_1,...,B_z
N = 16                                 # sum n_1 + ... + n_z -- where n_i is the length of the vector to prove norm <= B_i
n_bin = 0                              # length of the vector to prove binary coefficients 
approximate_norm_proof = 0             # boolean to indicate if we perform approximate norm proofs
B_approx = 1                           # bound B' for approximate norm proofs, ignored if the boolean is zero

# Parameters for rejection sampling
gamma1 = 0.73                          # rejection sampling for s1
gamma2 = 0.73                          # rejection sampling for s2
gamma3 = 4                             # rejection sampling for s3
gamma4 = 1                             # rejection sampling for s4 -- ignore if approximate_norm_proof = 0 

# Setting the standard deviations, apart from stdev2 
stdev1 = gamma1 * C1 * sqrt(alpha^2 + Z *d)
stdev2 = 0
stdev3 = gamma3 * sqrt(337) * sqrt( (n_bin+Z)*d + (B_sum)^2)
stdev4 = gamma4 * sqrt(337) * B_approx 

# Finding MLWE dimension
nu = 1                                 # randomness vector s2 with coefficients between -nu and nu
kmlwe = 20
#while findMLWEdelta(nu,kmlwe,d, logq) > 1.0045:
#    kmlwe += 1                         # increasing the value of kmlwe until MLWE provides ~ 128-bit security

# Finding an appropriate kmsis and gamma
kmsis = 0
secure = false
while secure == false:
    kmsis += 1
    m2 = kmlwe + kmsis + ell + lmbda/2 + 256/d + 1 + approximate_norm_proof * (256/d + 1) + 1           # here, we used the packing trick from Section 6.5.1.1
    stdev2 = gamma2 * C1 * nu * sqrt(m2 * d)
    Bound1 = 2 * stdev1 * sqrt(2 * (m1 + Z) * d)
    Bound2 = 2 * stdev2 * sqrt(2 * m2 * d)
    Bound = 4 * C1 * sqrt(Bound1^2 + Bound2^2)
    if findMSISdelta(Bound, kmsis, d, logq) < 1.0045 and Bound < 2^logq:
        secure = true

# Finding an appropriate compression variable gamma
gamma = 2^logq 
secure = false
while secure == false:
    gamma = gamma/2
    m2 = kmlwe + kmsis + ell + lmbda/2 + 256/d + 1 + approximate_norm_proof * (256/d + 1) + 1           # here, we used the packing trick from Section 6.5.1.1
    stdev2 = gamma2 * C1 * nu * sqrt((m2 - kmsis) * d)
    Bound1 = 2 * stdev1 * sqrt(2 * (m1 + Z) * d)
    Bound2 = 2 * sqrt ( 2 * stdev2^2  *  (m2 - kmsis) * d + (2*gamma + 1)^2 * kmsis * d)
    Bound = 4 * C1 * sqrt(Bound1^2 + Bound2^2)
    if findMSISdelta(Bound, kmsis, d, logq) < 1.0045 and Bound < 2^logq:
        secure = true


# Finding exact value for q, q1 and gamma and compression variables:
find_true_gamma = 0
q1 = 2^(logq1)
while find_true_gamma == 0:
    q1 =  4*l * int(2^(log(q1,2)) / (4*l)) + 2*l + 1            # we need q1 to be congruent to 2l+1 modulo 4l
    while is_prime(q1) == False :
        q1 -= 4*l
    if eta == 1:
        q = q1
    else:
        q2 = 4*l * int(2^(logq)/(4*l*q1)) + 2*l  + 1        # we need q2 to be congruent to 2l+1 modulo 4l
        while is_prime(q2) == False :
            q2 -= 4*l
        q = q1 * q2 
    Div_q = divisors( (q-1)/2)                                  # we want to find a divisor of (q-1)/2 close to gamma
    for i in Div_q:
        if gamma/2 <= i and i <= gamma:
            find_true_gamma = i
gamma = find_true_gamma 
D = log(2*gamma/(omega*d),2)
tau = omega * nu * d

# Checking soundness conditions
rho = sqrt( 1 - log(2^(-kappa)) / 128 )                 
Barp = 2 * sqrt(256/26) * rho * stdev3 

if q <  41 * (n_bin + N + Z) * d * Barp:
    print("ERROR: can't use Lemma 2.2.8")
if q <= Barp^2 + Barp*sqrt(n_bin*d):
    print("ERROR: can't prove P_s + P_m + f has binary coefficients")
if q <= Barp^2 + Barp*sqrt(d):
    print("ERROR: can't prove all \theta_i have binary coefficients")
for bound in BoundsToProve:
    if q <= 3 * bound^2 + Barp^2:
        print("ERROR: can't prove (6.12")


#Proof size
GaussEntr = 4.13
full_sized = kmsis * d * (logq - D) + (ell + 256/d + 1 + approximate_norm_proof * (256/d + 1) + lmbda + 1)* d * logq
short_size1 = (m1 + Z) * d * ceil(log(GaussEntr * stdev1,2)) + (m2 - kmsis) * d * ceil(log(GaussEntr * stdev2,2)) 
short_size2 = 256 * ceil(log(GaussEntr * stdev3,2)) + approximate_norm_proof * 256 * ceil(log(GaussEntr * stdev4,2))

print("Total proof size in KB: ", round((full_sized + short_size1 + short_size2)/(2^13) , 2))

#Final security analysis with exact parameters
rej_rate = exp(1/(2*gamma1^2)) * exp(1/(2*gamma2^2)) * exp(1/(2*gamma3^2)) * ((1-approximate_norm_proof) + approximate_norm_proof*exp(1/(2*gamma4^2)))
rej_rate *= exp( kmsis * (2*tau + 1) * d / (2 * gamma) )
print("Rejection rate: ", rej_rate.n())

Bound1 = 2 * stdev1 * sqrt(2 * (m1 + Z) * d)
Bound2 = 2 * sqrt ( 2 * stdev2^2  *  (m2 - kmsis) * d + (2*gamma + 1)^2 * kmsis * d)
Bound = 4 * C1 * sqrt(Bound1^2 + Bound2^2)
print("Root Hermite factor for MSIS: ", round(findMSISdelta(Bound, kmsis, d, logq),6)) 
