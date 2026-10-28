-- Prove2me | solution 1 for AvramDividend.Classical.killed_weight_nat_caps_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:25:50.169464+00:00
-- url     : https://prove2.me/submissions/5e674b95-2593-4f2e-8c20-7767eab915ab

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) := by 
  intro n
  exact Measurable.ite (measurableSet_le hT measurable_const) hw measurable_const
