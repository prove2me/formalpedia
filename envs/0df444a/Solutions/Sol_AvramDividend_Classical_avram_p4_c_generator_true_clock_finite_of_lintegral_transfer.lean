-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_true_clock_finite_of_lintegral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:39.94741+00:00
-- url     : https://prove2.me/submissions/bb9a0d01-0a7a-4761-9e22-8196e67e248c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual predictable physical clock is finite whenever its
genuine source product clock is finite and the exact lintegral transfer holds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)))
    (hsourceFinite :
      (((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) Set.univ) < ⊤) :
    IsFiniteMeasure μ := by
  have hmass : μ Set.univ =
      (((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) Set.univ) := by
    simpa only [lintegral_one] using
      (hμ (fun _ => (1 : ℝ≥0∞)) measurable_const)
  exact ⟨hmass.trans_lt hsourceFinite⟩
