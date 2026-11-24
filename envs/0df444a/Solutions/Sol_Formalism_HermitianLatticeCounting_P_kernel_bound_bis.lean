-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.kernel_bound_bis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:29.023622+00:00
-- url     : https://prove2.me/submissions/19f7f83b-728c-46e4-b6da-d9ab53318e26

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : KernelBound := by
  intro X ι _ μ _ _ F c hF horth y
  have hint : ∀ w w', Integrable (fun x => star (F w x) * F w' x) μ := by
    intro w w'
    exact (hF w).star.integrable_mul (hF w')
  have e : ∀ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ)
      = ∑ w, ∑ w', star (c w) * c w' * (star (F w x) * F w' x) := by
    intro x
    have : ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) = star (∑ w, c w * F w x) * ∑ w, c w * F w x := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w' _
    rw [star_mul']; ring
  have h1 : (∫ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∑ w, ‖c w‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [e]
    rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun w' _ => (hint w w').const_mul _))]
    push_cast
    apply Finset.sum_congr rfl; intro w _
    rw [integral_finsetSum _ (fun w' _ => (hint w w').const_mul _)]
    simp_rw [integral_const_mul, horth]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.star_def, Complex.conj_mul']
  rw [integral_complex_ofReal] at h1
  have h2 : (∫ x, ‖∑ w, c w * F w x‖ ^ 2 ∂μ) = ∑ w, ‖c w‖ ^ 2 := by exact_mod_cast h1
  rw [h2]
  calc ‖∑ w, c w * F w y‖ ^ 2 ≤ (∑ w, ‖c w‖ * ‖F w y‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end Formalism.HermitianLatticeCounting.P
