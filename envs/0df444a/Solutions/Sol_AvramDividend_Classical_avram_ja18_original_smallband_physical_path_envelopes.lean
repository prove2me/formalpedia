-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_smallband_physical_path_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:40:31.858471+00:00
-- url     : https://prove2.me/submissions/f8fd5237-a02a-4ad3-9d1a-a14911430d2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_uniform_count_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_cadlag_adapted_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The full physical small-band path inherits the same count envelope
as its finite cutoffs by closedness of the real norm bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω) ∧
      (∀ T : ℝ≥0, ∃ B : Ω → ℝ,
        Integrable B P ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Jsmall t ω‖ ≤ B ω) ∧
        (∀ k : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
          ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω)) := by
  obtain ⟨Jsmall, hLimit, hRight, hZero, hAdapt⟩ :=
    avram_ja18b_original_smallband_cadlag_adapted_limit X hX hFinite
  refine ⟨Jsmall, hLimit, hRight, hZero, hAdapt, ?_⟩
  intro T
  obtain ⟨B, hBint, hCutoffs⟩ :=
    avram_ja18b_original_smallband_uniform_count_envelope X hFinite T
  have hFull : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      ‖Jsmall t ω‖ ≤ B ω := by
    filter_upwards [hLimit, hCutoffs] with ω hωlim hωbound
    intro t ht
    exact le_of_tendsto (hωlim t).norm
      (Filter.Eventually.of_forall (fun k => hωbound k t ht))
  refine ⟨B, hBint, hFull, ?_⟩
  intro k
  filter_upwards [hCutoffs] with ω hω
  exact hω k
