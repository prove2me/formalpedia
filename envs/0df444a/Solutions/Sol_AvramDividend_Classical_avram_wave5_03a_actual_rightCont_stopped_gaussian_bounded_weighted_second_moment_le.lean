-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_second_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:12:28.262204+00:00
-- url     : https://prove2.me/submissions/831b3dd9-5e64-47b9-b468-06e6d0e63622

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine stopped source Gaussian cells have a variance bounded by their
    time-length and the original Lévy variance convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hHbound : ∀ ω, |H ω| ≤ K) :
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) ≤
      K ^ 2 * ((h : ℝ) * X.σ ^ 2) := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤ K ^ 2 * ((h : ℝ) * X.σ ^ 2)
  have hWeighted :
      (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
        K ^ 2 * (∫ ω, (Y ω) ^ 2 ∂P) := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
        X hν τ hτ T hbounded h H hHmeas K hK hHbound
  have hVariance :
      (∫ ω, (Y ω) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2 := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
        X hν τ hτ T hbounded h
  exact hWeighted.trans
    (mul_le_mul_of_nonneg_left hVariance (sq_nonneg K))
