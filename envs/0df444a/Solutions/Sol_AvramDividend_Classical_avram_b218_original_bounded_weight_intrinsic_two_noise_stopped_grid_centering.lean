-- Prove2me | solution 1 for AvramDividend.Classical.avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:31:11.205671+00:00
-- url     : https://prove2.me/submissions/497ed812-4bba-412f-98e9-596264589d6e

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

/-- Bounded original predictable source weights imply integrated initially centred stopped gains. -/
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
        (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
        (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
        (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ),
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
  intro ι S a b WG WJ hab hWG hWJ τ hτstop LG LJ hLG hLJ hWGbound hWJbound
  have hGprod (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) P := by
    have hMeas : MeasurableSet[𝓕.rightCont (a i)]
        {ω : Ω | τ ω ≤ a i} := by
      simpa only [WithTop.coe_le_coe] using hτstop (a i)
    have hf : AEStronglyMeasurable
        (fun ω => if τ ω ≤ a i then (0 : ℝ) else WG i ω) P :=
      ((Measurable.ite hMeas measurable_const (hWG i hi)).mono
        (𝓕.rightCont.le (a i)) le_rfl).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂P, ‖(if τ ω ≤ a i then (0 : ℝ) else WG i ω)‖ ≤ LG := by
      filter_upwards [] with ω
      by_cases hz : τ ω ≤ a i
      · simp [hz, hLG]
      · simpa [hz] using hWGbound i hi ω
    exact ((hRI (b i)).sub (hRI (a i))).bdd_mul hf hb
  have hJprod (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => (if τ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P := by
    have hMeas : MeasurableSet[𝓕.rightCont (a i)]
        {ω : Ω | τ ω ≤ a i} := by
      simpa only [WithTop.coe_le_coe] using hτstop (a i)
    have hf : AEStronglyMeasurable
        (fun ω => if τ ω ≤ a i then (0 : ℝ) else WJ i ω) P :=
      ((Measurable.ite hMeas measurable_const (hWJ i hi)).mono
        (𝓕.rightCont.le (a i)) le_rfl).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂P, ‖(if τ ω ≤ a i then (0 : ℝ) else WJ i ω)‖ ≤ LJ := by
      filter_upwards [] with ω
      by_cases hz : τ ω ≤ a i
      · simp [hz, hLJ]
      · simpa [hz] using hWJbound i hi ω
    exact ((hJI (b i)).sub (hJI (a i))).bdd_mul hf hb
  exact avram_jb21_original_two_channel_masked_initial_condexp
    S R Jsmall hRI hRM hJI hJM
    a b WG WJ hab hWG hWJ τ hτstop hGprod hJprod
