-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:11.581723+00:00
-- url     : https://prove2.me/submissions/1443c834-d4b4-47fd-b719-bce3b9771f72

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem solution {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : FunctionalInequalities.Analysis.BakryEmery.cutoff R x = 1 := by
    unfold FunctionalInequalities.Analysis.BakryEmery.cutoff
    apply (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).one_of_mem_closedBall
    have hdiv : ‖x‖ / R ≤ 1 := by
      exact (div_le_iff₀ hR).2 (by
        simpa only [one_mul] using hx)
    have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
      calc
        ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
          rw [norm_smul]
          simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        _ = ‖x‖ / R := by
          simp [div_eq_mul_inv, mul_comm]
        _ ≤ 1 := hdiv
    change dist (R⁻¹ • x) 0 ≤ 1
    simpa only [dist_zero_right] using hnorm
