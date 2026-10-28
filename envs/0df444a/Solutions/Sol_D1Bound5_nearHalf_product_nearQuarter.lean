-- Prove2me | solution 1 for D1Bound5.nearHalf_product_nearQuarter
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:47.673116+00:00
-- url     : https://prove2.me/submissions/d5dbc006-75c8-4a6b-a0e9-5cbc951dee5a

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



end D1Bound5

namespace D1Bound5

/-- Products of two entries near one half are near one quarter. -/
theorem _root_.solution (x y : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖x*y - (1/4 : ℂ)‖ < (1/40 : ℝ) := by
  let a := x - (1/2 : ℂ)
  let b := y - (1/2 : ℂ)
  have ha : ‖a‖ < (128/8649 : ℝ) := hx
  have hb : ‖b‖ < (128/8649 : ℝ) := hy
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
  have hproduct : ‖a‖*‖b‖ < (128/8649 : ℝ)^2 := by
    calc
      _ ≤ (128/8649 : ℝ)*‖b‖ :=
        mul_le_mul_of_nonneg_right ha.le (norm_nonneg _)
      _ < (128/8649 : ℝ)*(128/8649 : ℝ) :=
        mul_lt_mul_of_pos_left hb (by norm_num)
      _ = (128/8649 : ℝ)^2 := by ring
  have hlin : (1/2 : ℝ)*(‖a‖+‖b‖) < (128/8649 : ℝ) := by
    linarith only [ha, hb]
  have hn : (128/8649 : ℝ)^2 + (128/8649 : ℝ) < 1/40 := by norm_num
  linarith only [hbound, hproduct, hlin, hn]



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5
end
