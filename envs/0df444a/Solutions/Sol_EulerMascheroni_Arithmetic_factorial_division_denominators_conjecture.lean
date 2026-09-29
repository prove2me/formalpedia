-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.factorial_division_denominators_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:03:34.26551+00:00
-- url     : https://prove2.me/submissions/819d81fa-0378-4fff-8420-4a904f96f093
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Arithmetic_factorial_denominators_iff_prime_local_endpoints
import Theorems.Thm_EulerMascheroni_Arithmetic_gompertz_prime_local_bounds_conjecture
open EulerMascheroni.Arithmetic

theorem solution
    (h : IsAlgebraic ℚ EulerMascheroni.gompertzConstant) :
    EulerMascheroni.Arithmetic.ExponentialDenominators EulerMascheroni.gompertzConstant := by
  exact (factorial_denominators_iff_prime_local_endpoints EulerMascheroni.gompertzConstant).mpr
    (gompertz_prime_local_bounds_conjecture h)

#print axioms solution
