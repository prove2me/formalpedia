-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_positive_esscher_root_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:43:51.219586+00:00
-- url     : https://prove2.me/submissions/0fef5155-cd69-4394-b56a-4247c903d8c9

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A Standing spectrally negative Lévy process has a strictly positive
Laplace-exponent root at every strictly positive discount rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  by_cases hBV : X.BoundedVariation
  · exact bv_positive_esscher_root X hX q hq hBV
  · exact positive_esscher_root_of_unbounded_variation X hBV q hq
