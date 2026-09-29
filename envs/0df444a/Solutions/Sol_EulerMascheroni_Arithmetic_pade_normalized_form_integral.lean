-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_normalized_form_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:17:22.10631+00:00
-- url     : https://prove2.me/submissions/94f3b5b0-62ad-49a2-978a-b52c9e1e09b1

import Theorems.Thm_EulerMascheroni_Arithmetic_pade_binomial_identity
import Theorems.Thm_EulerMascheroni_Arithmetic_binomial_transform_integral
open EulerMascheroni.Arithmetic
namespace EulerNormalized
lemma integral_normalized_form (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2) := by
  rw [pade_binomial_identity]
  have heq : (d:ℝ)*((n.factorial:ℝ)^2*binomialTransform (quotientCoeff a) n)/(n.factorial:ℝ)^2 =
      (d:ℝ)*binomialTransform (quotientCoeff a) n := by field_simp
  rw [heq]
  exact binomial_transform_integral a n d h


end EulerNormalized


theorem solution (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2) := by
  exact EulerNormalized.integral_normalized_form a n d h

#print axioms solution
