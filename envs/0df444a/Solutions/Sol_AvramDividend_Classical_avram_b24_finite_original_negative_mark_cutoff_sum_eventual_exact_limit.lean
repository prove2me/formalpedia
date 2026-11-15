-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:06.983819+00:00
-- url     : https://prove2.me/submissions/6eaba333-d7d8-4fc0-88b7-cc3c7bb41ffa

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {α : Type*} (S : Finset α) (z : α → ℝ) :
    Tendsto (fun n : ℕ =>
      ∑ i ∈ S, if -1 < z i ∧
        z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0)
      atTop (𝓝 (∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0)) := by
  classical
  have hSum (s : Finset α) : ∀ᶠ n : ℕ in atTop,
      (∑ i ∈ s, if -1 < z i ∧
        z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0) =
      (∑ i ∈ s, if -1 < z i ∧ z i < 0 then z i else 0) := by
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (fun n => by simp)
    | @insert i s hi ih =>
        filter_upwards [
          AvramDividend.Classical.avram_b24_negative_mark_single_cutoff_eventually_equals_full_negative_indicator (z i),
          ih] with n hn hs
        simp only [Finset.sum_insert hi]
        rw [hn, hs]
  have hEq : (fun _ : ℕ => ∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0)
      =ᶠ[atTop]
      (fun n : ℕ => ∑ i ∈ S, if -1 < z i ∧
        z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0) :=
    by
      filter_upwards [hSum S] with n hn
      exact hn.symm
  exact tendsto_const_nhds.congr' hEq
