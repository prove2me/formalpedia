-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_positive_gaussian_witness_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:30:50.877278+00:00
-- url     : https://prove2.me/submissions/2691ec15-e63f-4183-bdd6-278005378166

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
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
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
  exact ⟨𝓕, Y, hYc, hYσ, hYν, hStanding, hUBV⟩
