-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.binomial_transform_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:17:19.685465+00:00
-- url     : https://prove2.me/submissions/16924757-755e-42fc-ac44-bb39e830d754

import Definitions.Def_eulerMascheroni_padeTransform
open EulerMascheroni.Arithmetic
namespace EulerIntegralTransform
lemma integral_transform (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*binomialTransform (quotientCoeff a) n) := by
  unfold binomialTransform
  rw [Finset.mul_sum]
  apply IsIntegral.sum
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hi := h (n+j) (by omega)
  have hw : IsIntegral ℤ (((n.choose j * (n+j).choose n : ℕ) : ℝ)) := isIntegral_natCast _
  convert hw.mul hi using 1 <;> ring


end EulerIntegralTransform


theorem solution (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*binomialTransform (quotientCoeff a) n) := by
  exact EulerIntegralTransform.integral_transform a n d h

#print axioms solution
