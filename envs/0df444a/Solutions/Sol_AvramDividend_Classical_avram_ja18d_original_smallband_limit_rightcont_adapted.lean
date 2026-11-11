-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18d_original_smallband_limit_rightcont_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:25:56.880038+00:00
-- url     : https://prove2.me/submissions/6a03b0a9-025a-4292-8928-1b1c468b2f28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_uniform_count_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ja18k_subsigma_dominated_ae_limit_meas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Apply the general dominated sub-sigma-algebra closure to the original
compensated small-jump cutoffs, using their same-space integrable count bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hLimit : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  let J (k : ℕ) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω
  have hSource : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => J k ω) atTop (𝓝 (Jsmall t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω t
  have hCutF (k : ℕ) :
      AEStronglyMeasurable[𝓕.rightCont t] (J k) P := by
    exact ((avram_anoise33_original_smallband_compensator_adapted
      X k t).mono (𝓕.le_rightCont t) le_rfl).aestronglyMeasurable
  have hCutAmbient (k : ℕ) : AEStronglyMeasurable (J k) P := by
    exact ((avram_anoise33_original_smallband_compensator_adapted
      X k t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  obtain ⟨B, hBi, hCutBound⟩ :=
    avram_ja18b_original_smallband_uniform_count_envelope X hFinite t
  have hNorm (k : ℕ) : ∀ᵐ ω ∂P, ‖J k ω‖ ≤ B ω := by
    filter_upwards [hCutBound] with ω hω
    exact hω k t le_rfl
  have hJMeas : AEStronglyMeasurable[𝓕.rightCont t] (Jsmall t) P :=
    avram_ja18k_subsigma_dominated_ae_limit_meas
      P (𝓕.rightCont t) (𝓕.rightCont.le t)
      J (Jsmall t) B hCutF hBi hNorm hSource
  have hJAmbient : AEStronglyMeasurable (Jsmall t) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hCutAmbient hSource
  have hJBound : ∀ᵐ ω ∂P, ‖Jsmall t ω‖ ≤ B ω := by
    filter_upwards [hSource, hCutBound] with ω hωlim hωbound
    exact le_of_tendsto hωlim.norm
      (Filter.Eventually.of_forall (fun k => hωbound k t le_rfl))
  have hJInt : Integrable (Jsmall t) P :=
    Integrable.mono' hBi hJAmbient hJBound
  exact condExp_of_aestronglyMeasurable'
    (𝓕.rightCont.le t) hJMeas hJInt
