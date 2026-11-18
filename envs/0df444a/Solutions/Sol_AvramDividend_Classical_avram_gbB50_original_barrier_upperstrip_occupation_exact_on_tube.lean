-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:34:58.721761+00:00
-- url     : https://prove2.me/submissions/8c0fe582-da6c-4658-9a22-9c085df49ccd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB48_original_barrier_upperstrip_occupation_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_barrier_upperstrip_section_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The physical upper-strip occupation is the full horizon on the original tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (hTn : (T : ℝ) ≤ n)
    (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ)) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (T : ℝ) ∧
        (5 / 44 : ℝ) <
          riskProcess X (1 / 8 : ℝ)
            (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) = (T : ℝ) := by
  exact avram_gbB48_original_barrier_upperstrip_occupation_on_tube
    X n T hT hTn ω hTube
    (avram_gbB49_original_barrier_upperstrip_section_measurable X T ω)
