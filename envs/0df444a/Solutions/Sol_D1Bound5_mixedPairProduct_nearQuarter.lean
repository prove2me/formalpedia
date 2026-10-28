-- Prove2me | solution 1 for D1Bound5.mixedPairProduct_nearQuarter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:01.677006+00:00
-- url     : https://prove2.me/submissions/13dd4248-306a-4268-b060-3af6faff5efb

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5

/-- A product of a first-row and a later-row normalized root entry lies
within 7/192 of one quarter. The two error radii are different. -/
theorem _root_.solution (x y : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖x*y - (1/4 : ℂ)‖ < (7/192 : ℝ) := by
  let a := x - (1/2 : ℂ)
  let b := y - (1/2 : ℂ)
  have ha : ‖a‖ < (1/18 : ℝ) := hx
  have hb : ‖b‖ < (1/64 : ℝ) := hy
  have hid : x*y - (1/4 : ℂ) =
      a*b + (1/2 : ℂ)*a + (1/2 : ℂ)*b := by
    dsimp [a,b]
    ring
  have hbound : ‖x*y - (1/4 : ℂ)‖ ≤
      ‖a‖*‖b‖ + (1/2 : ℝ)*(‖a‖+‖b‖) := by
    rw [hid]
    calc
      ‖a*b + (1/2 : ℂ)*a + (1/2 : ℂ)*b‖
          ≤ ‖a*b + (1/2 : ℂ)*a‖ + ‖(1/2 : ℂ)*b‖ := norm_add_le _ _
      _ ≤ (‖a*b‖ + ‖(1/2 : ℂ)*a‖) + ‖(1/2 : ℂ)*b‖ := by
          have h := norm_add_le (a*b) ((1/2 : ℂ)*a)
          linarith only [h]
      _ = ‖a‖*‖b‖ + (1/2 : ℝ)*(‖a‖+‖b‖) := by
          simp
          ring
  have hproduct : ‖a‖*‖b‖ < (1/18 : ℝ)*(1/64) := by
    calc
      _ ≤ (1/18 : ℝ)*‖b‖ :=
        mul_le_mul_of_nonneg_right ha.le (norm_nonneg _)
      _ < (1/18 : ℝ)*(1/64) :=
        mul_lt_mul_of_pos_left hb (by norm_num)
  have hlin : (1/2 : ℝ)*(‖a‖+‖b‖) <
      (1/2)*(1/18+1/64) := by
    linarith only [ha, hb]
  have hn : (1/18 : ℝ)*(1/64) + (1/2)*(1/18+1/64) = 7/192 := by
    norm_num
  linarith only [hbound, hproduct, hlin, hn]





end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
