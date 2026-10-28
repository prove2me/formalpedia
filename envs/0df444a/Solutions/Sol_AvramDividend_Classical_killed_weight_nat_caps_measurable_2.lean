-- Prove2me | solution 2 for AvramDividend.Classical.killed_weight_nat_caps_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:25:53.125617+00:00
-- url     : https://prove2.me/submissions/ec2d5154-023d-4004-b156-fbe6b3b6dbb7

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) := by
  intro n
  exact Measurable.ite (measurableSet_le hT measurable_const)
    hw measurable_const