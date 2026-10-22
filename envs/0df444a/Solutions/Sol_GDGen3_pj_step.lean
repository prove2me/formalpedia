-- Prove2me | solution 1 for GDGen3.pj_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:20:39.992396+00:00
-- url     : https://prove2.me/submissions/02f27072-b6f7-4e85-a4bc-74d4d9cd4084

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring
