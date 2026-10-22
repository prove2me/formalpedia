-- Prove2me | solution 2 for GDGen3.quadratic_root_lt
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:37:12.492397+00:00
-- url     : https://prove2.me/submissions/fea36219-5425-45a5-8f05-f6603b9658cd

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_quadratic_root_le

noncomputable section

open Finset

open GDGen3

theorem solution (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 < p * y ^ 2 + b * y - X) : x < y := by
  have hle := quadratic_root_le p b X x y hp hX hx hy hroot (le_of_lt hq)
  have hne : x ≠ y := by intro he; subst y; linarith
  exact lt_of_le_of_ne hle hne
