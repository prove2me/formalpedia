-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:52:09.123145+00:00
-- url     : https://prove2.me/submissions/80ff6729-9ba9-4610-840c-c7f6da086034

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
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
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, MG ω + MJ ω ∂P) = 0)
      := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, hR, hJ, hGrids⟩ :=
    avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
      X hX hFinite
  refine ⟨R, Jsmall, hR, hJ, ?_⟩
  intro ι S a b WG WJ hab hWG hWJ τ hτstop LG LJ hLG hLJ hWGbound hWJbound
  let MG : Ω → ℝ := fun ω =>
    ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) *
      (R (b i) ω - R (a i) ω)
  let MJ : Ω → ℝ := fun ω =>
    ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)
  obtain ⟨hMGI, hMGzero, hMJI, hMJzero⟩ :=
    hGrids S a b WG WJ hab hWG hWJ τ hτstop LG LJ hLG hLJ
      hWGbound hWJbound
  refine ⟨hMGI, hMGzero, hMJI, hMJzero, ?_⟩
  intro A hA
  have hPositive : MeasurableSet[𝓕.rightCont 0]
      {η : Ω | τ η ≠ 0} :=
    avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
      τ hτstop
  have hEvent : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {η : Ω | τ η ≠ 0}) := hA.inter hPositive
  have hMGzeroEvent :
      (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, MG ω ∂P) = 0 :=
    avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      MG hMGI hMGzero (A ∩ {η : Ω | τ η ≠ 0}) hEvent
  have hMJzeroEvent :
      (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, MJ ω ∂P) = 0 :=
    avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      MJ hMJI hMJzero (A ∩ {η : Ω | τ η ≠ 0}) hEvent
  rw [MeasureTheory.integral_add hMGI.integrableOn hMJI.integrableOn,
    hMGzeroEvent, hMJzeroEvent]
  ring
