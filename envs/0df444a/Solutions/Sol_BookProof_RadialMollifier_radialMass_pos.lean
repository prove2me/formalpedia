-- Prove2me | solution 1 for BookProof.RadialMollifier.radialMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:45:34.397245+00:00
-- url     : https://prove2.me/submissions/47f9f061-bd96-4f41-a474-3a0e0cc5ae11

-- Generated from ChapterRadialMollifier.lean — theorem BookProof.RadialMollifier.radialMass_pos
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier



open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section
open BookProof.RadialMollifier

theorem solution: 0 < radialMass := by
  unfold radialMass
  have hnn : ∀ z : ℂ, 0 ≤ radialBump z := fun z => expNegInvGlue.nonneg _
  have hc : Continuous radialBump := by
    unfold radialBump
    exact (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_const.sub Complex.continuous_normSq)
  have hcs : HasCompactSupport radialBump := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) ?_
    intro z hz
    unfold radialBump
    apply expNegInvGlue.zero_of_nonpos
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    have h1 : 1 < Complex.normSq z := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith
    linarith
  have hi : MeasureTheory.Integrable radialBump := hc.integrable_of_hasCompactSupport hcs
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg hnn hi]
  have hsub : Metric.ball (0 : ℂ) 1 ⊆ Function.support radialBump := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz
    rw [Function.mem_support]
    apply ne_of_gt
    unfold radialBump
    apply expNegInvGlue.pos_of_pos
    have h1 : Complex.normSq z < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    linarith
  exact lt_of_lt_of_le (Metric.measure_ball_pos _ _ one_pos) (MeasureTheory.measure_mono hsub)
