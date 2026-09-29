-- Prove2me | solution 1 for Freiman.approximationValue_integer_translate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:17.48898+00:00
-- url     : https://prove2.me/submissions/3a7ad3b3-3f24-4bfa-ba7c-5e5207dffce0

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_integerDistance_integer_translate

open Freiman

theorem solution (ξ : ℝ) (z : ℤ) (q : ℕ) :
    approximationValue (ξ + (z : ℝ)) q = approximationValue ξ q := by
  unfold approximationValue
  have h : (q : ℝ) * (ξ + (z : ℝ)) = (q : ℝ) * ξ + ((q : ℤ) * z : ℤ) := by push_cast; ring
  rw [h, integerDistance_integer_translate]
