-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_finite_mark_eapprox_pullback
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:06:13.937683+00:00
-- url     : https://prove2.me/submissions/7ed28698-6dc6-4156-9978-a9fb63d9ed42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux20_monotone_finite_mark_sum_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Simple mark approximants converge on a finite time-indexed jump set. -/
theorem solution
    {α β : Type*} [MeasurableSpace β]
    (S : Finset α) (mark : α → β)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (⨆ n : ℕ, ∑ u ∈ S,
      MeasureTheory.SimpleFunc.eapprox g n (mark u)) =
      ∑ u ∈ S, g (mark u) := by
  classical
  have hm : ∀ u, Monotone (fun n : ℕ =>
      MeasureTheory.SimpleFunc.eapprox g n (mark u)) := by
    intro u i j hij
    exact (MeasureTheory.SimpleFunc.monotone_eapprox g hij) (mark u)
  rw [avram_redux20_monotone_finite_mark_sum_iSup
    S (fun n u => MeasureTheory.SimpleFunc.eapprox g n (mark u)) hm]
  apply Finset.sum_congr rfl
  intro u hu
  exact MeasureTheory.SimpleFunc.iSup_eapprox_apply hg (mark u)
