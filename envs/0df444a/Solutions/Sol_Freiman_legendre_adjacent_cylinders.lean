-- Prove2me | solution 1 for Freiman.legendre_adjacent_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:17.515473+00:00
-- url     : https://prove2.me/submissions/d8dde6ee-4e44-4f61-8d75-135a154721eb

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_rational_adjacent_radius
import Theorems.Thm_Freiman_rational_two_cylinder_cover

open Freiman

theorem solution (w : List ℕ+) (hw : w ≠ []) (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) (b : ℕ → ℕ+) :
    |cfValue b - finiteCF w| < 1 / (2 * (wordContinuantQ w : ℝ)^2) →
      ∃ n : ℕ, cfConvergent b n = finiteCF w := by
  intro hx
  exact rational_two_cylinder_cover w hw hlast b (rational_adjacent_radius w hw hlast (cfValue b) hx)
