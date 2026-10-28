-- Prove2me | solution 1 for AvramDividend.Classical.finite_time_set_has_monotone_zero_started_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:21:09.672481+00:00
-- url     : https://prove2.me/submissions/55deedf5-71ef-42c3-9b99-7c93fe19e22f

import Mathlib
open scoped NNReal

theorem solution
    (J : Finset ℝ≥0) :
    ∃ t : ℕ → ℝ≥0, Monotone t ∧ t 0 = 0 ∧
      ∃ n : ℕ, ∀ j : J, ∃ i : Fin n, t (i.val + 1) = j.1 := by
  classical
  let e := J.orderEmbOfFin rfl
  let t : ℕ → ℝ≥0 := fun k =>
    if k = 0 then 0 else if h : k - 1 < J.card then e ⟨k - 1, h⟩ else J.sup id
  have hle : ∀ i : Fin J.card, e i ≤ J.sup id := fun i =>
    Finset.le_sup (f := id) (J.orderEmbOfFin_mem rfl i)
  refine ⟨t, monotone_nat_of_le_succ fun k => ?_, by simp [t], J.card, fun j => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [t]
    · have hk1 : k + 1 ≠ 0 := by omega
      have hk0 : k ≠ 0 := by omega
      simp only [t, hk1, hk0, if_false, Nat.add_sub_cancel]
      by_cases h1 : k < J.card
      · have h0 : k - 1 < J.card := by omega
        rw [dif_pos h0, dif_pos h1]
        exact e.monotone (Fin.mk_le_mk.2 (by omega))
      · rw [dif_neg h1]
        split_ifs with h0
        · exact hle _
        · exact le_rfl
  · obtain ⟨i, hi⟩ : ∃ i, e i = j.1 := by
      have := J.range_orderEmbOfFin rfl
      have hj : j.1 ∈ Set.range e := by rw [this]; exact j.2
      exact hj
    refine ⟨i, ?_⟩
    simp only [t, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, dif_pos i.2]
    exact hi
