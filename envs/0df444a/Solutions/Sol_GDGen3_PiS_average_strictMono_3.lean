-- Prove2me | solution 3 for GDGen3.PiS_average_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:36:21.078759+00:00
-- url     : https://prove2.me/submissions/66581342-4771-4fc8-af06-5ba9369d5a66

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_PiS_next_strict

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => PiS r (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have ht := PiS_next_strict r hr hr1 (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at ht ⊢
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  simp only [PiS, sum_range_succ] at *
  nlinarith
