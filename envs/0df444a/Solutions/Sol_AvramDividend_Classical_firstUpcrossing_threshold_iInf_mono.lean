-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_threshold_iInf_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:25:08.200837+00:00
-- url     : https://prove2.me/submissions/4edf3b60-ce18-4772-b8cd-ca976e4612f2

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- A higher pathwise threshold cannot be reached earlier in the
extended-real first-upcrossing infimum, including unreachable levels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hbc : b ≤ c) :
    (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) ≤
    (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞)) := by
  refine le_iInf fun r => le_iInf fun hcr => ?_
  exact iInf_le_of_le r
    ((iInf_le (fun (_ : b < X.X r ω) => (r : ℝ≥0∞)))
      (lt_of_le_of_lt hbc hcr))
