-- Prove2me | solution 2 for GDGen3.M_gap
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:34:31.067433+00:00
-- url     : https://prove2.me/submissions/78adea17-ccb5-4abf-95b9-3c05cb7d0d24

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_PiS_closed

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 + r) - M r N =
      ((1 + (N : ℝ) * (1 + r)) ^ 2 - 1 / r ^ (2 * N)) /
        ((1 + r) * (N : ℝ) * ((N : ℝ) + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  unfold M
  rw [PiS_closed r hr hr1 N]
  unfold pj
  field_simp
  ring
