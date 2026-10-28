-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:19.848835+00:00
-- url     : https://prove2.me/submissions/887b6a53-ea4c-457e-b49a-e7391df8971b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem solution {R : ℝ} (hR : 0 < R) : HasCompactSupport (FunctionalInequalities.Analysis.BakryEmery.cutoff (E := E) R) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) ?_
    intro x hx
    have hxnorm : 2 * R < ‖x‖ := by
      have hnot : ¬‖x‖ ≤ 2 * R := by
        intro h
        apply hx
        simpa [Metric.closedBall, dist_zero_right] using h
      exact lt_of_not_ge hnot
    have hscale : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hmul : R⁻¹ * (2 * R) < R⁻¹ * ‖x‖ :=
      mul_lt_mul_of_pos_left hxnorm (inv_pos.mpr hR)
    have heq : R⁻¹ * (2 * R) = 2 := by
      calc
        R⁻¹ * (2 * R) = 2 * (R⁻¹ * R) := by ring
        _ = 2 := by rw [inv_mul_cancel₀ hR.ne', mul_one]
    have hnotball : R⁻¹ • x ∉ Metric.ball (0 : E) 2 := by
      intro h
      have hlt : ‖R⁻¹ • x‖ < 2 := by
        simpa [Metric.ball, dist_zero_right] using h
      rw [hscale, ← heq] at hlt
      exact (not_lt_of_ge (le_of_lt hmul)) hlt
    have hs :
        Function.support (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) =
          Metric.ball (0 : E) 2 := by
      simpa [FunctionalInequalities.Analysis.BakryEmery.unitBump] using
        (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).support_eq
    by_contra hne
    apply hnotball
    rw [← hs]
    exact hne
