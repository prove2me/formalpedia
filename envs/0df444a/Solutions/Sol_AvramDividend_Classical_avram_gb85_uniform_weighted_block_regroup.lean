-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb85_uniform_weighted_block_regroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:03:53.057198+00:00
-- url     : https://prove2.me/submissions/de2cadd7-f37a-4880-8994-084139f549d7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Group a finite sum into consecutive blocks of length b. -/
theorem solution (m b : ℕ) (hb : 0 < b) (f g : ℕ → ℝ) :
    (Finset.range ((m + 1) * b)).sum (fun r => g (r / b) * f r) =
    (Finset.range (m + 1)).sum (fun i =>
      g i * (Finset.range b).sum (fun j => f (i * b + j))) := by
  induction m with
  | zero =>
      simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.zero_add,
        Finset.sum_range_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Nat.div_eq_of_lt (Finset.mem_range.mp hj)]
  | succ m ih =>
      have hN : (m + 1 + 1) * b = (m + 1) * b + b := by ring
      have hq (j : ℕ) (hj : j < b) : ((m + 1) * b + j) / b = m + 1 := by
        calc
          ((m + 1) * b + j) / b = (j + (m + 1) * b) / b := by rw [Nat.add_comm]
          _ = j / b + (m + 1) := Nat.add_mul_div_right j (m + 1) hb
          _ = m + 1 := by simp [Nat.div_eq_of_lt hj]
      have hblock :
        (Finset.range b).sum (fun j =>
            g (((m + 1) * b + j) / b) * f ((m + 1) * b + j)) =
          g (m + 1) * (Finset.range b).sum (fun j =>
              f ((m + 1) * b + j)) := by
        calc
          _ = (Finset.range b).sum (fun j =>
                g (m + 1) * f ((m + 1) * b + j)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [hq j (Finset.mem_range.mp hj)]
          _ = _ := by rw [Finset.mul_sum]
      calc
        (Finset.range ((m + 1 + 1) * b)).sum (fun r => g (r / b) * f r) =
            (Finset.range (m + 1)).sum (fun i =>
              g i * (Finset.range b).sum (fun j => f (i * b + j))) +
            (Finset.range b).sum (fun j =>
              g (((m + 1) * b + j) / b) * f ((m + 1) * b + j)) := by
              rw [hN, Finset.sum_range_add, ih]
        _ = (Finset.range (m + 1)).sum (fun i =>
              g i * (Finset.range b).sum (fun j => f (i * b + j))) +
            g (m + 1) * (Finset.range b).sum (fun j =>
              f ((m + 1) * b + j)) := by rw [hblock]
        _ = _ := (Finset.sum_range_succ (fun i =>
              g i * (Finset.range b).sum (fun j => f (i * b + j))) (m + 1)).symm
