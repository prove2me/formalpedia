-- Prove2me | solution 3 for GDGen3.PiS_closed
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:32:24.340785+00:00
-- url     : https://prove2.me/submissions/37611b41-925d-4aba-b843-bed4a8a88078

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_step

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  induction i with
  | zero => simp [PiS, pj]
  | succ i ih =>
    have hp := pj_step r (ne_of_gt hr) i
    change PiS r (i + 1) = _
    rw [PiS, sum_range_succ]
    change PiS r i + pj r (i + 1) = _
    rw [ih]
    push_cast
    field_simp [hne]
    nlinarith [hp]
