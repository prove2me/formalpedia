-- Prove2me | solution 2 for AvramDividend.Classical.avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:54.688208+00:00
-- url     : https://prove2.me/submissions/f8633a87-f75d-45fe-bea2-a805360163cf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
theorem solution
    {α : Type*} (S : Finset α) (z : α → ℝ) :
    Tendsto (fun n : ℕ =>
      ∑ i ∈ S, if -1 < z i ∧
        z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0)
      atTop (𝓝 (∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0))  := by
  have hcut : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  apply tendsto_finset_sum S
  intro i hiS
  by_cases hi : -1 < z i ∧ z i < 0
  · have he : ∀ᶠ n : ℕ in atTop,
        z i < -(1 / ((n : ℝ) + 1)) :=
      hcut.eventually_const_lt hi.2
    have heq : (fun n : ℕ =>
        if -1 < z i ∧ z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0) =ᶠ[atTop]
        fun _ => z i := by
      filter_upwards [he] with n hn
      exact if_pos ⟨hi.1, hn.le⟩
    exact (Filter.tendsto_congr' heq).2 (by simpa [hi] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z i) atTop (𝓝 (z i))))
  · have hnever (n : ℕ) :
        ¬ (-1 < z i ∧ z i ≤ -(1 / ((n : ℝ) + 1))) := by
      intro hn
      have hden : 0 < (n : ℝ) + 1 := by positivity
      have hneg : -(1 / ((n : ℝ) + 1)) < 0 :=
        neg_neg_of_pos (one_div_pos.mpr hden)
      exact hi ⟨hn.1, lt_of_le_of_lt hn.2 hneg⟩
    have heq : (fun n : ℕ =>
      if -1 < z i ∧ z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      exact if_neg (hnever n)
    rw [heq]
    simpa only [if_neg hi] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
