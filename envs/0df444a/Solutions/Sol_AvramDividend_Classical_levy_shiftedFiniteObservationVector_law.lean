-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedFiniteObservationVector_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:44:34.70801+00:00
-- url     : https://prove2.me/submissions/affb8ec3-2571-4251-aff7-f6bc817b94fa

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_AvramDividend_Classical_levy_shiftedConsecutiveIncrement_vector_law
import Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_zeroBasedGrid_law
import Theorems.Thm_AvramDividend_Classical_levy_gridPosition_law_implies_finiteIndex_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- All finite-dimensional Lévy position vectors are stationary under deterministic time shifts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) (J : Finset ℝ≥0) :
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (s + (j : ℝ≥0)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  obtain ⟨n, t, e, ht, ht0, he⟩ := finiteTimeSet_monotoneZeroBasedGrid J
  have hIncr := levy_shiftedConsecutiveIncrement_vector_law X s t ht n
  have hGrid := levy_incrementVector_law_implies_zeroBasedGrid_law
    X s t ht0 n hIncr
  exact levy_gridPosition_law_implies_finiteIndex_law
    X s t n J e he hGrid
