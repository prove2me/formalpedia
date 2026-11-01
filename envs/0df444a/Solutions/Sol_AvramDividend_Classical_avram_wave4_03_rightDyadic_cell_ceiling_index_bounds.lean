-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:49:42.80028+00:00
-- url     : https://prove2.me/submissions/0572cd51-6b78-4e17-ae6a-257bc01a8af1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
/-- Exact ceiling cell index bounds on the positive unit interval,
needed to identify the original-source dyadic Stieltjes step kernel. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let k := Nat.ceil (y * (N : ℝ))
    0 < k ∧ k ≤ N ∧ ((k : ℝ) - 1) < y * (N : ℝ) ∧
      y * (N : ℝ) ≤ (k : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < y * (N : ℝ) := mul_pos hy hNr
  have hlo : y * (N : ℝ) ≤ (Nat.ceil (y * (N : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hhi : (Nat.ceil (y * (N : ℝ)) : ℝ) <
      y * (N : ℝ) + 1 :=
    Nat.ceil_lt_add_one hp.le
  have hkpos : 0 < Nat.ceil (y * (N : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le hp hlo)
  have hkle : Nat.ceil (y * (N : ℝ)) ≤ N := by
    apply (Nat.ceil_le).2
    nlinarith [mul_le_mul_of_nonneg_right hy1 hNr.le]
  dsimp
  refine ⟨hkpos, hkle, ?_, hlo⟩
  linarith
