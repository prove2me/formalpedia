-- Prove2me | solution 1 for Freiman.prefixEval_difference
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:30.418115+00:00
-- url     : https://prove2.me/submissions/d8b617e5-ccc6-41ce-98c6-a86e513db2cd

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_mobius_determinant_difference_algebra
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_determinant

open Freiman

theorem solution (w : List ℕ+) (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |prefixEval w x - prefixEval w y| = |x - y| /
      (((wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w) *
       ((wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w)) := by
  rw [prefixEval_mobius w x hx.1, prefixEval_mobius w y hy.1]
  apply mobius_determinant_difference_algebra
  · exact_mod_cast continuant_denominator_pos w
  · positivity
  · exact hx.1
  · exact hy.1
  · have hz := congrArg abs (continuant_determinant w)
    have hz' : |(wordContinuantPrevP w:ℤ)*wordContinuantQ w-
        (wordContinuantP w:ℤ)*wordContinuantPrevQ w|=1 := by simpa using hz
    exact_mod_cast hz' 
