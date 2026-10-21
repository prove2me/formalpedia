-- Prove2me | solution 1 for AvramDividend.Classical.measurable_finite_mass_bin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:39:24.012605+00:00
-- url     : https://prove2.me/submissions/43794491-0a68-4589-a6c1-f950fb35a47f

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : Ω → ℝ≥0∞) (hm : Measurable m) (n : ℕ) :
    MeasurableSet
      {ω : Ω | m ω ≤ (n + 1 : ℝ≥0∞) ∧
        (n = 0 ∨ (n : ℝ≥0∞) < m ω)} := by
  have hUpper : MeasurableSet
      {ω : Ω | m ω ≤ (n + 1 : ℝ≥0∞)} :=
    measurableSet_Iic.preimage hm
  have hLower : MeasurableSet
      {ω : Ω | n = 0 ∨ (n : ℝ≥0∞) < m ω} := by
    by_cases hn : n = 0
    · simpa [hn] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    · have hIoi : MeasurableSet
          {ω : Ω | (n : ℝ≥0∞) < m ω} :=
        measurableSet_Ioi.preimage hm
      simpa [hn] using hIoi
  exact hUpper.inter hLower
