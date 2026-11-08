-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian15_original_stop_coefficient_L2_energy_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:16:20.582441+00:00
-- url     : https://prove2.me/submissions/dea3d368-32a2-4a2d-b4e0-4816e6b76d25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- An L²-small difference of original stopped-history Gaussian coefficients
has a vanishing physical stopped Gaussian increment square budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G : ℕ → Ω → ℝ) (H : Ω → ℝ)
    (hG : ∀ n,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G n))
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : ∀ n, Measurable (G n))
    (hHglobal : Measurable H)
    (hCoeff : Tendsto (fun n =>
      ∫ ω, (G n ω - H ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      ((G n ω - H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hEq (n : ℕ) :
      (∫ ω, ((G n ω - H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (G n ω - H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) :=
    avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket
      X hν τ hτ T hbounded h (G n) H (hG n) hH (hGglobal n) hHglobal
  have hfun :
      (fun n => ∫ ω, ((G n ω - H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
      (fun n => (∫ ω, (G n ω - H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2)) := by
    funext n
    exact hEq n
  rw [hfun]
  simpa only [zero_mul] using hCoeff.mul_const ((h : ℝ) * X.σ ^ 2)
