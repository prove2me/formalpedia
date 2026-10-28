-- Prove2me | solution 2 for AvramDividend.Classical.levy_shiftedFiniteObservationVector_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:45:02.816526+00:00
-- url     : https://prove2.me/submissions/e3236509-2c02-4d94-8cb1-629a856cef10

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_AvramDividend_Classical_levy_shiftedConsecutiveIncrement_vector_law
import Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_zeroBasedGrid_law
import Theorems.Thm_AvramDividend_Classical_levy_gridPosition_law_implies_finiteIndex_law

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) (J : Finset ℝ≥0) :
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  obtain ⟨n, t, e, ht, ht0, he⟩ := AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid J
  exact AvramDividend.Classical.levy_gridPosition_law_implies_finiteIndex_law X s t n J e he
    (AvramDividend.Classical.levy_incrementVector_law_implies_zeroBasedGrid_law X s t ht0 n
      (AvramDividend.Classical.levy_shiftedConsecutiveIncrement_vector_law X s t ht n))
