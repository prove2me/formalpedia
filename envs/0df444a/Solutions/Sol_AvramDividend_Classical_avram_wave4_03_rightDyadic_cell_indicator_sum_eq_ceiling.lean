-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:16:01.82347+00:00
-- url     : https://prove2.me/submissions/762412a5-f70f-4e2b-86af-21ff4e17cc16

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Right-ceiling grid step is its unique half-open cell contribution. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range N,
      if (i : ℝ) < y * (N : ℝ) ∧
        y * (N : ℝ) ≤ ((i + 1 : ℕ) : ℝ) then a (i + 1) else 0) =
    a (Nat.ceil (y * (N : ℝ))) := by
  classical
  obtain ⟨hkpos, hkle, hklo, hkhi⟩ :=
    avram_wave4_03_rightDyadic_cell_ceiling_index_bounds y hy hy1 N hN
  let k := Nat.ceil (y * (N : ℝ))
  have hkone : k - 1 + 1 = k := by omega
  have hkr : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    exact_mod_cast hkone
  have hkcond : ((k - 1 : ℕ) : ℝ) < y * (N : ℝ) ∧
      y * (N : ℝ) ≤ (((k - 1 + 1 : ℕ) : ℝ)) := by
    constructor
    · change (k : ℝ) - 1 < y * (N : ℝ) at hklo
      linarith
    · simpa only [hkone] using hkhi
  rw [Finset.sum_eq_single (k - 1)]
  · rw [if_pos hkcond, hkone]
  · intro i hi hne
    by_cases hicond : (i : ℝ) < y * (N : ℝ) ∧
        y * (N : ℝ) ≤ ((i + 1 : ℕ) : ℝ)
    · have hik : i < k := by
        have hr : (i : ℝ) < (k : ℝ) := lt_of_lt_of_le hicond.1 hkhi
        exact_mod_cast hr
      have hki : k < i + 2 := by
        have hr : (k : ℝ) < ((i + 2 : ℕ) : ℝ) := by
          push_cast
          change (k : ℝ) - 1 < y * (N : ℝ) at hklo
          have hupper : y * (N : ℝ) ≤ (i : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hicond.2
          linarith [hupper]
        exact_mod_cast hr
      have : i = k - 1 := by omega
      exact (hne this).elim
    · simp only [if_neg hicond]
  · intro hnot
    have hmem : k - 1 ∈ Finset.range N := by
      apply Finset.mem_range.mpr
      omega
    exact (hnot hmem).elim
