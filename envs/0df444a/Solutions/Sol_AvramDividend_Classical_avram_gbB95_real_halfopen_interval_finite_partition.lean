-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB95_real_halfopen_interval_finite_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:58:15.57225+00:00
-- url     : https://prove2.me/submissions/0acd4687-aca5-4e22-8468-eb96a091596b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (a δ t : ℝ) (hδ : 0 < δ) (b : ℕ) :
    (if a ≤ t ∧ t < a + (b : ℝ) * δ then (1 : ℝ) else 0) =
    (Finset.range b).sum (fun j =>
      if a + (j : ℝ) * δ ≤ t ∧
        t < a + ((j + 1 : ℕ) : ℝ) * δ
      then (1 : ℝ) else 0) := by
  induction b with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero,
        Finset.sum_range_zero]
      split_ifs with h
      · exact (False.elim ((not_lt_of_ge h.1) h.2))
      · rfl
  | succ b ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [Nat.cast_succ]
      have hb : 0 ≤ (b : ℝ) * δ :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)
      have heq : a + ((b : ℝ) + 1) * δ =
          a + (b : ℝ) * δ + δ := by ring
      rw [heq]
      by_cases ha : a ≤ t
      · by_cases hb' : t < a + (b : ℝ) * δ
        · have htbig : t < a + (b : ℝ) * δ + δ := by linarith
          have hnot : ¬ a + (b : ℝ) * δ ≤ t := not_le_of_gt hb'
          simp [ha, hb', htbig, hnot]
        · have hge : a + (b : ℝ) * δ ≤ t := le_of_not_gt hb'
          by_cases htbig : t < a + (b : ℝ) * δ + δ
          · simp [ha, hb', hge, htbig]
          · simp [ha, hb', hge, htbig]
      · have hnot : ¬ a + (b : ℝ) * δ ≤ t := by
          intro h
          have hlow : a ≤ a + (b : ℝ) * δ := by linarith [hb]
          exact ha (hlow.trans h)
        simp [ha, hnot]
