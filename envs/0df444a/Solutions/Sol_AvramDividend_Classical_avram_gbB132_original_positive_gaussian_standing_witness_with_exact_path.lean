-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:40:54.403747+00:00
-- url     : https://prove2.me/submissions/a5badef6-26c3-4d29-af23-6bb2f006f2fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB29_positive_drift_gaussian_sigma1_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_positive_gaussian_standing_and_unbounded_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The native Gaussian source retains its exact Brownian-plus-drift formula. -/
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation := by
  obtain ⟨𝓕, Y, hYpath, hYc, hYσ, hYν⟩ :=
    avram_gbB29_positive_drift_gaussian_sigma1_witness
  have hI : Integrable (Y.X 1) gaussianLimit := by
    have hbase :=
      avram_wave3_04_gaussian_drifted_unit_integrable
    have hconst : Integrable
        (fun (_ : ℝ≥0 → ℝ) => (3 : ℝ)) gaussianLimit :=
      integrable_const 3
    have hsum := hbase.add hconst
    have heq : Y.X 1 = (fun ω : ℝ≥0 → ℝ =>
        (brownian 1 ω - brownian 0 ω - (1 : ℝ)) + 3) := by
      funext ω
      rw [hYpath]
      norm_num
      ring
    rw [heq]
    exact hsum
  obtain ⟨hStanding, hUBV⟩ :=
    positive_gaussian_standing_and_unbounded_variation Y
      (by rw [hYσ]; norm_num) hI
  exact ⟨𝓕, Y, hYpath, hYc, hYσ, hYν, hStanding, hUBV⟩
