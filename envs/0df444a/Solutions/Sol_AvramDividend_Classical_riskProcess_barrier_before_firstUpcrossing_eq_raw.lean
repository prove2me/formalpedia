-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_before_firstUpcrossing_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:46:45.515663+00:00
-- url     : https://prove2.me/submissions/fabb2154-f1f2-4555-be73-ec802c720118

import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Before the first strict upper passage, cumulative dividends vanish and
    the controlled reserve equals the uncontrolled Lévy capital process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (ht : t < u) :
    riskProcess X x (barrierStrategy X x a) t ω = x + X.X t ω := by
  have hbelow : ∀ s : ℝ≥0, s ≤ t → X.X s ω ≤ a - x := by
    intro s hst
    exact firstUpcrossing_prethreshold_le X (a - x) ω u hu s
      (lt_of_le_of_lt hst ht)
  have hzero := barrierStrategy_zero_before_upcrossing X x a t ω hbelow
  simp [riskProcess, hzero]
