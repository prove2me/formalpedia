-- Prove2me | solution 1 for AvramDividend.Classical.avram_b217_original_global_intrinsic_two_noise_stopped_grid_initial_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:02:05.037917+00:00
-- url     : https://prove2.me/submissions/33b8f3f4-60b4-4307-af2f-0301f64ecfd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Global original same-source two-noise centring for all genuine stopped finite grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
 :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      ∀ {ι : Type*} (S : Finset ι)
        (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
        (hab : ∀ i ∈ S, a i ≤ b i)
        (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
        (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
        (τ : Ω → ℝ≥0)
        (hτstop : IsStoppingTime 𝓕.rightCont
          (fun ω => (τ ω : WithTop ℝ≥0)))
        (hGprod : ∀ i ∈ S, Integrable
          (fun ω => (if τ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) P)
        (hJprod : ∀ i ∈ S, Integrable
          (fun ω => (if τ ω ≤ a i then 0 else WJ i ω) *
            (Jsmall (b i) ω - Jsmall (a i) ω)) P),
      let MG : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      let MJ : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)
      Integrable MG P ∧
      P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable MJ P ∧
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, M, hRlim, hJlim, hRI, hJI,
    hRM, hJM, hSource⟩ :=
    avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
      X hX hFinite
  refine ⟨R, Jsmall, hRlim, hJlim, ?_⟩
  intro ι S a b WG WJ hab hWG hWJ τ hτstop hGprod hJprod
  exact avram_jb21_original_two_channel_masked_initial_condexp
    S R Jsmall hRI hRM hJI hJM
    a b WG WJ hab hWG hWJ τ hτstop hGprod hJprod
