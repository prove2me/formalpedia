-- Prove2me | solution 1 for DerivativeChainContinuation.sixth9_actual_root_family
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:42:03.146304+00:00
-- url     : https://prove2.me/submissions/f89d2fbe-fc2b-4587-a678-75484823fb3b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth9_validated_inverse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation
open Polynomial
 theorem sixth_unit_source_expansion (β : ℂ) :
    ((X^3-X-C β)^6 : Polynomial ℂ)=
      C (1)*X^18 +
      C (-6)*X^16 +
      C (-6*β)*X^15 +
      C (15)*X^14 +
      C (30*β)*X^13 +
      C (15*β^2 - 20)*X^12 +
      C (-60*β)*X^11 +
      C (15 - 60*β^2)*X^10 +
      C (-20*β^3 + 60*β)*X^9 +
      C (90*β^2 - 6)*X^8 +
      C (60*β^3 - 30*β)*X^7 +
      C (15*β^4 - 60*β^2 + 1)*X^6 +
      C (-60*β^3 + 6*β)*X^5 +
      C (-30*β^4 + 15*β^2)*X^4 +
      C (-6*β^5 + 20*β^3)*X^3 +
      C (15*β^4)*X^2 +
      C (6*β^5)*X^1 +
      C (β^6)*X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

theorem sixth_unit_row9_inverse_identity (β z : ℂ) (hz : z ≠ 0) :
    (derivative^[9] ((X^3-X-C β)^6)).eval z =
      3628800*z^9*sixth9G ((z⁻¹)^2) (β/z^3) := by
  rw [sixth_unit_source_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial,sixth9G,sixth9G0,sixth9G1,sixth9G2]
  field_simp [hz]
  <;> ring

theorem sixth_unit_row9_of_inverse (β z : ℂ) (hz : z ≠ 0)
    (h : sixth9G ((z⁻¹)^2) (β/z^3)=0) :
    (derivative^[9] ((X^3-X-C β)^6)).eval z=0 := by
  rw [sixth_unit_row9_inverse_identity β z hz,h,mul_zero]
end DerivativeChainContinuation

theorem solution :
    ∃ W : ℂ → ℂ,
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      (∀ t : ℂ,‖t‖ ≤ 2 → ‖W t-sixth9P t‖ ≤ 1/100000000 ∧ sixth9G t (W t)=0) ∧
      (∀ x : ℝ,|x| ≤ 2 → (W (x:ℂ)).im=0) ∧
      ∀ z : ℂ,z ≠ 0 → ‖z⁻¹‖^2 ≤ 2 →
        (derivative^[9] ((X^3-X-C (z^3*W ((z⁻¹)^2)))^6)).eval z=0 := by
  obtain ⟨W,hW,hhol,hreal⟩ := sixth9_validated_inverse
  refine ⟨W,hhol,hW,hreal,?_⟩
  intro z hz ht
  apply sixth_unit_row9_of_inverse _ z hz
  have ht' : ‖(z⁻¹)^2‖ ≤ 2 := by simpa only [norm_pow] using ht
  simpa only [mul_div_cancel_left₀ _ (pow_ne_zero 3 hz)] using (hW ((z⁻¹)^2) ht').2
