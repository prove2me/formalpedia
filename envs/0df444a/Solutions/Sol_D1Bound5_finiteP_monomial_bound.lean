-- Prove2me | solution 1 for D1Bound5.finiteP_monomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:58.6809+00:00
-- url     : https://prove2.me/submissions/9a553e05-d2cb-4f78-9dc3-6209bb3698a2

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

section
namespace D1Bound5

/-- A common scalar bound for both the leading and tail terms of P.
The exponent condition records exactly how much reciprocal-anchor decay
remains after allowing two powers of the largest anchor. -/
theorem _root_.solution (A S U V : ℝ) (q n d e : ℕ)
    (hA1 : 1 ≤ A) (hAU : A ≤ U) (hAV : A ≤ V)
    (hUS : U ≤ S) (hVS : V ≤ S) (he : e ≤ 2)
    (hsum : d+e+q ≤ n+2) :
    U^d*V^e/U^n ≤ S^2/A^q := by
  have hA : 0 < A := by linarith only [hA1]
  have hU1 : 1 ≤ U := hA1.trans hAU
  have hV1 : 1 ≤ V := hA1.trans hAV
  have hS1 : 1 ≤ S := hU1.trans hUS
  have hU : 0 < U := by linarith only [hU1]
  have hV : 0 ≤ V := by linarith only [hV1]
  have hS : 0 ≤ S := by linarith only [hS1]
  have hleft : U^d*V^e*A^q ≤ U^(d+q)*S^e := by
    calc
      _ ≤ U^d*S^e*U^q := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hright : U^(d+q)*S^e ≤ U^n*S^2 := by
    by_cases hp : d+q ≤ n
    · exact mul_le_mul (pow_le_pow_right₀ hU1 hp)
        (pow_le_pow_right₀ hS1 he) (by positivity) (by positivity)
    · have hnp : n ≤ d+q := by omega
      have hremain : d+q-n+e ≤ 2 := by omega
      calc
        _ = U^n*(U^(d+q-n)*S^e) := by
          conv_lhs => rw [show d+q=n+(d+q-n) by omega, pow_add]
          ring
        _ ≤ U^n*(S^(d+q-n)*S^e) := by gcongr
        _ = U^n*S^(d+q-n+e) := by rw [pow_add]
        _ ≤ U^n*S^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 hremain) (by positivity)
  apply (div_le_div_iff₀ (pow_pos hU n) (pow_pos hA q)).mpr
  convert hleft.trans hright using 1 <;> ring

end D1Bound5
end
