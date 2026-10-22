-- Prove2me | solution 2 for GDGen3.X_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:33:42.433583+00:00
-- url     : https://prove2.me/submissions/650ce4f9-760d-4e41-9256-afcbe7c489bd

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    X r N (i + 1) - X r N i = pj r (i + 1) * C r N i := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold X C
  rw [PiS, sum_range_succ]
  change (M r N * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) / 2
      - (1 - r) * (PiS r i + pj r (i + 1))) / (1 + r)
    - (M r N * (i : ℝ) * ((i : ℝ) + 1) / 2 - (1 - r) * PiS r i) / (1 + r) = _
  push_cast
  field_simp [hp]
  ring
