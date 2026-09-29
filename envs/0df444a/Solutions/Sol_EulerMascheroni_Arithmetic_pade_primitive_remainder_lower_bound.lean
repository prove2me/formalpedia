-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_primitive_remainder_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:37:51.068012+00:00
-- url     : https://prove2.me/submissions/3c9a9bfe-5907-43f0-a1fe-953beff6b188

import Theorems.Thm_EulerMascheroni_Arithmetic_pade_exact_cancellation
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_positive_remainder_and_lower_bound
open EulerMascheroni.Arithmetic

theorem solution (n K : ℕ) (hK : 0 < K) :
    ((n+1).factorial:ℝ)*(K:ℝ)^(n+1) /
      (((K:ℝ)+1)^(n+1) * 3^(K+1) * ((K:ℝ)+2) *
        (Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2):ℝ)) ≤
    ((padeQ (n+1):ℝ)*EulerMascheroni.gompertzConstant-(padeP (n+1):ℝ)) /
      (Int.gcd (padeP (n+1)) (padeQ (n+1)):ℝ) := by
  rw [(pade_exact_cancellation n).1]
  rw [← div_div]
  exact div_le_div_of_nonneg_right
    ((pade_positive_remainder_and_lower_bound (n+1)).2.2 K hK) (Nat.cast_nonneg _)

#print axioms solution
