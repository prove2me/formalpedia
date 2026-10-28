-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_levy_positive_upward_increment_measure_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:54:16.085646+00:00
-- url     : https://prove2.me/submissions/8f83d560-abc7-40dd-93ad-88b36fd474c5

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure_all_times
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- An unbounded-variation spectrally negative Lévy process has a positive
chance of a strictly positive increment at every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation) :
    ∀ t : ℝ≥0, 0 < t → 0 < P {ω : Ω | 0 < X.X t ω} := by
  obtain ⟨β₀, hβ₀, hlarge⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  exact positive_psi_implies_upward_increment_positive_measure_all_times
    X β₀ hβ₀ (lt_trans hq (hlarge β₀ le_rfl))
