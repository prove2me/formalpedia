-- Prove2me | solution 1 for D1Bound5.mixedThreePairDet_norm_lt_33_128
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:49.304289+00:00
-- url     : https://prove2.me/submissions/4bba495a-8c8e-489f-86ec-4e2d0ee60220

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
import Theorems.Thm_D1Bound5_threePair_quadratic_norm_le

section
open Matrix

namespace D1Bound5



/-- The sharper determinant threshold used in Lemma product-five.
It improves the previously established 3/10 bound using the exact
nine-term quadratic estimate rather than a 13-term majorant. -/
theorem _root_.solution (P Q R : ℂ)
    (hP : ‖P - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hQ : ‖Q - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hR : ‖R - (1/4 : ℂ)‖ < (7/192 : ℝ)) :
    ‖P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R)‖ <
      (33/128 : ℝ) := by
  let a := P - (1/4 : ℂ)
  let b := Q - (1/4 : ℂ)
  let c := R - (1/4 : ℂ)
  have ha : ‖a‖ ≤ (7/192 : ℝ) := hP.le
  have hb : ‖b‖ ≤ (7/192 : ℝ) := hQ.le
  have hc : ‖c‖ ≤ (7/192 : ℝ) := hR.le
  have hsum : ‖a+b+c‖ ≤ (7/64 : ℝ) := by
    have h := norm_add_le (a+b) c
    have h' := norm_add_le a b
    linarith only [h, h', ha, hb, hc]
  have hquad := threePair_quadratic_norm_le a b c (7/192)
    (by norm_num) ha hb hc
  have hpoly :
      P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R) =
        -(3/16 : ℂ) - (a+b+c)/2 +
          (a^2+b^2+c^2 - 2*(a*b+a*c+b*c)) := by
    dsimp [a,b,c]
    ring
  rw [hpoly]
  have hhalf : ‖(a+b+c)/2‖ = ‖a+b+c‖/2 := by simp
  have h1 := norm_add_le (-(3/16 : ℂ) - (a+b+c)/2)
    (a^2+b^2+c^2-2*(a*b+a*c+b*c))
  have h2 := norm_sub_le (-(3/16 : ℂ)) ((a+b+c)/2)
  have hconstant : ‖-(3/16 : ℂ)‖ = (3/16 : ℝ) := by norm_num
  have hmain : ‖-(3/16 : ℂ) - (a+b+c)/2 +
      (a^2+b^2+c^2-2*(a*b+a*c+b*c))‖ ≤
      (3/16 : ℝ) + (7/64)/2 + 9*(7/192)^2 := by
    rw [hhalf] at h2
    rw [hconstant] at h2
    linarith only [h1, h2, hsum, hquad]
  exact lt_of_le_of_lt hmain (by norm_num)





end D1Bound5
end
