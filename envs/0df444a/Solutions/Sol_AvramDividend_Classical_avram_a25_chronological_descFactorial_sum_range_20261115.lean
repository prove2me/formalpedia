-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_chronological_descFactorial_sum_range_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:56:49.599537+00:00
-- url     : https://prove2.me/submissions/23abd4a2-fba1-43d6-b458-108cd02e3d12

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_chronological_descFactorial_step_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Nat AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- Ordered physical jumps sum the factorial weights of the preceding count. -/
theorem solution (m n : ℕ) :
    (n + 1) * (∑ k ∈ Finset.range m, Nat.descFactorial k n) =
      Nat.descFactorial m (n + 1) := by
  induction m with
  | zero => simp [Nat.zero_descFactorial_succ]
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      exact (avram_a25_chronological_descFactorial_step_20261115 m n).symm
