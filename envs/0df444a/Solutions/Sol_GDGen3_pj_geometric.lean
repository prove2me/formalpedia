-- Prove2me | solution 1 for GDGen3.pj_geometric
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:18:25.348148+00:00
-- url     : https://prove2.me/submissions/b8e3949b-2547-40f0-ab5c-5afed3989260

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
