-- Prove2me | solution 1 for GDGen3.nat_prefix_weight
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:20:08.79815+00:00
-- url     : https://prove2.me/submissions/a616bf8c-325e-49b4-a79c-e33dffdccbf9

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (n : ℕ) :
    2 * (∑ k ∈ range n, ((k : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
