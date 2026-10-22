-- Prove2me | solution 2 for GDGen3.rootE_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:38:35.485606+00:00
-- url     : https://prove2.me/submissions/12285d8d-6e02-469c-9173-378546bf88d4

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootE_one
import Theorems.Thm_GDGen3_rootE_step

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [rootE_one r hr]
    have hd : 0 < 1 - r := by linarith
    positivity
  | succ i hi ih =>
    have hp : 1 < 1 / r ^ (i + 1) := by
      apply (lt_div_iff₀ (pow_pos hr _)).2
      simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
    have hstep := rootE_step r hr i
    have hg : 0 < (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
      have hd : 0 < 1 - r := by linarith
      have hp' : 0 < 1 / r ^ (i + 1) - 1 := by linarith
      positivity
    linarith
