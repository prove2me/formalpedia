-- Prove2me | solution 1 for GDGen3.quadratic_root_le
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:34:23.006619+00:00
-- url     : https://prove2.me/submissions/59ca5e7d-0436-483d-9c2e-b6a0984e1699

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 ≤ p * y ^ 2 + b * y - X) : x ≤ y := by
  by_contra hle
  have hxy : y - x < 0 := by linarith
  have hpos : 0 < p * x * y + X := by positivity
  have he : x * (p * y ^ 2 + b * y - X) = (y - x) * (p * x * y + X) := by
    linear_combination y * hroot
  have hneg := mul_neg_of_neg_of_pos hxy hpos
  have hnon := mul_nonneg (le_of_lt hx) hq
  rw [he] at hnon
  linarith
