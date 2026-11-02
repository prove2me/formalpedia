-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:19:39.457309+00:00
-- url     : https://prove2.me/submissions/2fd98c2e-f125-4269-ad3e-851069b49ed0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    Filter.Tendsto
      (fun h : ℝ≥0 =>
        (∫ ω, (H ω *
          (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  classical
  let Y : ℝ≥0 → Ω → ℝ := fun h ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change Filter.Tendsto (fun h : ℝ≥0 => ∫ ω, (H ω * Y h ω) ^ 2 ∂P)
    (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ))
  have hlo (h : ℝ≥0) : 0 ≤
      (∫ ω, (H ω * Y h ω) ^ 2 ∂P) :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hhi (h : ℝ≥0) :
      (∫ ω, (H ω * Y h ω) ^ 2 ∂P) ≤
        (K ^ 2 * X.σ ^ 2) * (h : ℝ) := by
    have hWeighted : (∫ ω, (H ω * Y h ω) ^ 2 ∂P) ≤
        K ^ 2 * (∫ ω, (Y h ω) ^ 2 ∂P) := by
      simpa only [Y] using
        avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
          X hν τ hτ T hbounded h H hHmeas K hK hH
    have hVariance : (∫ ω, (Y h ω) ^ 2 ∂P) ≤
        (h : ℝ) * X.σ ^ 2 := by
      simpa only [Y] using
        avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
          X hν τ hτ T hbounded h
    calc
      (∫ ω, (H ω * Y h ω) ^ 2 ∂P) ≤
          K ^ 2 * (∫ ω, (Y h ω) ^ 2 ∂P) := hWeighted
      _ ≤ K ^ 2 * ((h : ℝ) * X.σ ^ 2) :=
        mul_le_mul_of_nonneg_left hVariance (sq_nonneg _)
      _ = (K ^ 2 * X.σ ^ 2) * (h : ℝ) := by ring
  have hlim : Filter.Tendsto
      (fun h : ℝ≥0 => (K ^ 2 * X.σ ^ 2) * (h : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    have ht := (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul
      (K ^ 2 * X.σ ^ 2)
    simpa only [NNReal.coe_zero, mul_zero] using ht
  exact squeeze_zero' (Filter.Eventually.of_forall hlo)
    (Filter.Eventually.of_forall hhi) hlim
