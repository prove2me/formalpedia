-- Prove2me | solution 2 for GDGen3.M_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:33:10.8655+00:00
-- url     : https://prove2.me/submissions/372b7190-2d23-458e-a8cf-9b1360768f58

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    0 < M r N := by
  have hPi : 0 < PiS r N := by
    unfold PiS
    apply sum_pos'
    · intro k hk; exact le_of_lt (pj_pos r hr hr1 (k + 1) (by omega))
    · exact ⟨0, mem_range.mpr (by omega), pj_pos r hr hr1 1 (by omega)⟩
  unfold M
  apply div_pos
  · positivity
  · have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    positivity
