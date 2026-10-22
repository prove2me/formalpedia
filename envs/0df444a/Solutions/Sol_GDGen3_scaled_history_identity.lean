-- Prove2me | solution 1 for GDGen3.scaled_history_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:47:09.441437+00:00
-- url     : https://prove2.me/submissions/84d08f19-4308-4b63-ae24-b5a9fba5e10f

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (N : ℕ) (a s : ℝ) (f q : ℕ → ℝ) :
    smallK N a (fun i => s * f i) (fun i => s ^ 2 * q i) = s * scaledK N a s f q := by
  unfold smallK scaledK
  simp only [mul_sub, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  ring
