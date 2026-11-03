-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_full_value_iff_barrier_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:53:47.849189+00:00
-- url     : https://prove2.me/submissions/999e77e8-e446-4847-9fd1-05565fa95419

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact source-agnostic all-strategy cap-zero value allowance iff
the original zero-barrier value fits the same allowance, without any
variation or Lévy-activity restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      dividendValue X q 0 D ≤ A) ↔
    dividendValue X q 0 (barrierStrategy X 0 0) ≤ A := by
  constructor
  · intro hAll
    have hBarrier : IsAdmissibleLe X 0 (0 : ℝ≥0∞)
        (barrierStrategy X 0 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (barrierStrategy_admissibleLe_nonnegative_barrier
          X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
    exact hAll (barrierStrategy X 0 0) hBarrier
  · intro hBudget D hD
    exact
      (zero_cap_admissible_dividendValue_le_barrier_at_zero
        X hX q hq D hD).trans hBudget
