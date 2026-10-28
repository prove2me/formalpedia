-- Prove2me | solution 1 for D1Bound5.threePair_quadratic_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:42.658983+00:00
-- url     : https://prove2.me/submissions/382444b8-1655-4f9f-9d34-cbf784a0aad5

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

/-- The quadratic remainder in the three-pair four-by-four determinant
has the sharp coefficient nine when all three errors have size <= epsilon. -/
theorem _root_.solution (a b c : ℂ) (epsilon : ℝ)
    (he : 0 ≤ epsilon)
    (ha : ‖a‖ ≤ epsilon) (hb : ‖b‖ ≤ epsilon) (hc : ‖c‖ ≤ epsilon) :
    ‖a^2 + b^2 + c^2 - 2*(a*b + a*c + b*c)‖ ≤
      9*epsilon^2 := by
  have hsq : ‖a^2 + b^2 + c^2‖ ≤
      ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by
    calc
      _ ≤ ‖a^2 + b^2‖ + ‖c^2‖ := norm_add_le _ _
      _ ≤ ‖a^2‖ + ‖b^2‖ + ‖c^2‖ := by
        have h := norm_add_le (a^2) (b^2)
        linarith only [h]
      _ = _ := by simp [norm_pow]
  have hprod : ‖a*b + a*c + b*c‖ ≤
      ‖a‖*‖b‖ + ‖a‖*‖c‖ + ‖b‖*‖c‖ := by
    calc
      _ ≤ ‖a*b + a*c‖ + ‖b*c‖ := norm_add_le _ _
      _ ≤ ‖a*b‖ + ‖a*c‖ + ‖b*c‖ := by
        have h := norm_add_le (a*b) (a*c)
        linarith only [h]
      _ = _ := by simp [norm_mul]
  have htri : ‖a^2 + b^2 + c^2 - 2*(a*b + a*c + b*c)‖ ≤
      ‖a‖^2 + ‖b‖^2 + ‖c‖^2 +
        2*(‖a‖*‖b‖ + ‖a‖*‖c‖ + ‖b‖*‖c‖) := by
    have h := norm_sub_le (a^2+b^2+c^2) ((2:ℂ)*(a*b+a*c+b*c))
    have ht : ‖(2:ℂ)*(a*b+a*c+b*c)‖ =
        2*‖a*b+a*c+b*c‖ := by
      simp [norm_mul]
    rw [ht] at h
    linarith only [h, hsq, hprod]
  have ha2 : ‖a‖^2 ≤ epsilon^2 :=
    (sq_le_sq₀ (norm_nonneg _) he).mpr ha
  have hb2 : ‖b‖^2 ≤ epsilon^2 :=
    (sq_le_sq₀ (norm_nonneg _) he).mpr hb
  have hc2 : ‖c‖^2 ≤ epsilon^2 :=
    (sq_le_sq₀ (norm_nonneg _) he).mpr hc
  have hab : ‖a‖*‖b‖ ≤ epsilon^2 := by
    calc
      _ ≤ epsilon*‖b‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ epsilon*epsilon := mul_le_mul_of_nonneg_left hb he
      _ = epsilon^2 := by ring
  have hac : ‖a‖*‖c‖ ≤ epsilon^2 := by
    calc
      _ ≤ epsilon*‖c‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ epsilon*epsilon := mul_le_mul_of_nonneg_left hc he
      _ = epsilon^2 := by ring
  have hbc : ‖b‖*‖c‖ ≤ epsilon^2 := by
    calc
      _ ≤ epsilon*‖c‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ epsilon*epsilon := mul_le_mul_of_nonneg_left hc he
      _ = epsilon^2 := by ring
  linarith only [htri, ha2, hb2, hc2, hab, hac, hbc]







end D1Bound5
end
