-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:19.984909+00:00
-- url     : https://prove2.me/submissions/64a353ae-a83f-43af-8bc9-4ccb25e997a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_lintegral_comp_invMap
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (ψ : ℝ → ℂ) :
    ∫⁻ x, ENNReal.ofReal (‖chartW ψ x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖ψ y‖ ^ 2) := by

  have key := lintegral_comp_invMap (fun y => ENNReal.ofReal (‖ψ y‖ ^ 2))
  rw [← key]
  refine lintegral_congr fun x => ?_
  have hnorm : ‖chartW ψ x‖ ^ 2 = (x ^ 2)⁻¹ * ‖ψ (invMap x)‖ ^ 2 := by
    simp only [chartW, norm_mul, norm_inv, Complex.norm_real, mul_pow, inv_pow,
      Real.norm_eq_abs, sq_abs]
  rw [hnorm, ENNReal.ofReal_mul (by positivity)]
