-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_concrete_gaussian_levy_source_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:04:28.184763+00:00
-- url     : https://prove2.me/submissions/ec6a22dc-51fc-47cd-9ca9-55c4e6bd701a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_natural_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_filtered_indep
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_stationary_all
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine spectrally negative Lévy process with a Gaussian part exists. -/
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      X.X = (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) =>
        brownian t ω - brownian 0 ω - (t : ℝ)) ∧
      X.c = -1 ∧ X.σ = 1 ∧ X.ν = 0 := by
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun t ω => brownian t ω - brownian 0 ω - (t : ℝ)
  obtain ⟨hmeas, hadapt⟩ := canonical_drifted_brownian_natural_adapted
  obtain ⟨hmeas', hindep'⟩ := avram_wave3_04_canonical_drifted_brownian_filtered_indep
  let 𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
    Filtration.natural B hmeas
  have hindep : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω : ℝ≥0 → ℝ => B t ω - B s ω) inferInstance)
        (𝓕 s) gaussianLimit := by
    intro s t hst
    exact hindep' s t hst
  have hstat : ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib
        (fun ω : ℝ≥0 → ℝ => B t ω - B s ω)
        (fun ω : ℝ≥0 → ℝ =>
          brownian (t - s) ω - brownian 0 ω - ((t - s : ℝ≥0) : ℝ))
        gaussianLimit gaussianLimit := by
    intro s t hst
    exact avram_wave3_04_canonical_drifted_brownian_stationary_all s t hst
  obtain ⟨X, hX, hc, hσ, hν⟩ :=
    avram_wave3_04_canonical_brownian_levy_constructor_of_increment_laws
      𝓕 hadapt hindep hstat
  exact ⟨𝓕, X, hX, hc, hσ, hν⟩
