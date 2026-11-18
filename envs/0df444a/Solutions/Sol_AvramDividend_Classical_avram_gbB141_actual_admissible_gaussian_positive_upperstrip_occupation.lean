-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB141_actual_admissible_gaussian_positive_upperstrip_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:01:16.133265+00:00
-- url     : https://prove2.me/submissions/ec82285d-cdad-4c87-aef1-275c134cdd21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_exact_gaussian_tube_positive_fixed_band_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Actual original HJB Gaussian source: cap occupation is positive on the tube. -/
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
          |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        0 < ∫ t in Ioo (0 : ℝ) (1 : ℝ),
          if t < (1 / 1000 : ℝ) ∧
              (5 / 44 : ℝ) <
                riskProcess Y (1 / 8 : ℝ)
                  (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume) := by
  obtain ⟨𝓕, Y, hpath, hStand, hUBV, h0, hcont, hneg, hC2, hGen,
      hAdm⟩ :=
    avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
  refine ⟨𝓕, Y, hpath, hStand, hUBV, hAdm, ?_⟩
  intro ω hTube
  exact avram_gbB60_exact_gaussian_tube_positive_fixed_band_occupation
    Y ω hTube
