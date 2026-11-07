-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_generic_measurable_mark_rectangle_encard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:35:02.500441+00:00
-- url     : https://prove2.me/submissions/589bbdbf-f8b2-4196-9d01-90a9bd327e7a

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (Y : ℝ≥0 → ℝ)
    (hMark : Measurable (fun u : ℝ≥0 =>
      (u, Y u - Function.leftLim Y u)))
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      Y u - Function.leftLim Y u ≠ 0 ∧
      Y u - Function.leftLim Y u ∈ B}).encard := by
  let j : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  have hj : Measurable j := measurable_snd.comp hMark
  have hpos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hnonzero : MeasurableSet {u : ℝ≥0 | j u ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hS : MeasurableSet {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} :=
    hpos.inter hnonzero
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) := hMark
  have hrect : MeasurableSet (Ioc s t ×ˢ B) := measurableSet_Ioc.prod hB
  have hpre : MeasurableSet ((fun u : ℝ≥0 => (u, j u)) ⁻¹'
      (Ioc s t ×ˢ B)) := hrect.preimage hF
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u => (u, j u))) (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧ j u ≠ 0 ∧ j u ∈ B}).encard
  rw [Measure.map_apply hF hrect]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hS)]
  apply congrArg (fun T : Set ℝ≥0 => (T.encard : ℝ≥0∞))
  ext u
  simp [Set.mem_prod, Set.mem_preimage, Set.mem_inter_iff, j,
    and_assoc, and_left_comm, and_comm]
