-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_finsum_of_negative_unit_marks_le_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:31:54.793016+00:00
-- url     : https://prove2.me/submissions/643048b0-0283-4cf0-99f9-aed989767d2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {α : Type*} [DecidableEq α] (F : Finset α) (g : α → ℝ)
    (hlo : ∀ u ∈ F, -1 ≤ g u)
    (hhi : ∀ u ∈ F, g u ≤ 0) :
    |∑ u ∈ F, g u| ≤ (F.card : ℝ) := by
  classical
  have hnonpos : (∑ u ∈ F, g u) ≤ 0 := by
    exact Finset.sum_nonpos (fun u hu => hhi u hu)
  have hlower : -(F.card : ℝ) ≤ ∑ u ∈ F, g u := by
    have h := Finset.sum_le_sum (s := F)
      (fun u hu => hlo u hu)
    simpa using h
  rw [abs_of_nonpos hnonpos]
  linarith
