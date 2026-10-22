-- Prove2me | solution 2 for GDGen3.pj_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:19:37.384576+00:00
-- url     : https://prove2.me/submissions/83271f2a-d9b9-4385-b8d1-41ff62e02512

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    pj r j = ((1 / r ^ 2) ^ j - 1) / 2 := by
  unfold pj
  simp only [div_pow, one_pow, ← pow_mul]
  field_simp
