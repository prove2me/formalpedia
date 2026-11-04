-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:46:31.323435+00:00
-- url     : https://prove2.me/submissions/97f8a7a2-2114-439d-99c2-19264cee201f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- A finite count of independently measurable marked predicates is measurable. -/
theorem solution {Ω α : Type*} [mΩ : MeasurableSpace Ω]
    [DecidableEq α] (s : Finset α) (marked : α → Ω → Prop)
    (hMarked : ∀ i, MeasurableSet {ω : Ω | marked i ω}) :
    Measurable (fun ω : Ω =>
      (((s.filter (fun i => marked i ω)).card : ℕ) : ℝ≥0∞)) := by
  classical
  have hsum : Measurable (fun ω : Ω =>
      ∑ i ∈ s, if marked i ω then (1 : ℝ≥0∞) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hMarked i) measurable_const measurable_const
  convert hsum using 1
  funext ω
  exact avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
    s (fun i => marked i ω)
