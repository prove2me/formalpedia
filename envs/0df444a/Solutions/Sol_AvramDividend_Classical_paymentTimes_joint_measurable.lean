-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:32:41.696971+00:00
-- url     : https://prove2.me/submissions/175e3f7e-e733-4f20-9cf2-91eedb0852d1

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ) :
    MeasurableSet {p : ℝ × Ω | p.1 ∈ paymentTimes (τ p.2)} := by
  change MeasurableSet
    {p : ℝ × Ω | 0 ≤ p.1 ∧
      (p.1 = 0 ∨ ENNReal.ofReal p.1 < τ p.2)}
  have hfst : Measurable (fun p : ℝ × Ω => p.1) := measurable_fst
  have hsnd : Measurable (fun p : ℝ × Ω => τ p.2) :=
    hτ.comp measurable_snd
  have hnonneg : MeasurableSet
      {p : ℝ × Ω | 0 ≤ p.1} :=
    measurableSet_Ici.preimage hfst
  have hzero : MeasurableSet
      {p : ℝ × Ω | p.1 = 0} := by
    change MeasurableSet
      ((fun p : ℝ × Ω => p.1) ⁻¹' ({0} : Set ℝ))
    exact (MeasurableSet.singleton (0 : ℝ)).preimage hfst
  have hbefore : MeasurableSet
      {p : ℝ × Ω | ENNReal.ofReal p.1 < τ p.2} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp hfst) hsnd
  exact hnonneg.inter (hzero.union hbefore)
