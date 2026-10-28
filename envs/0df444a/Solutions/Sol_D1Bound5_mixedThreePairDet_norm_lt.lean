-- Prove2me | solution 1 for D1Bound5.mixedThreePairDet_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:53.381901+00:00
-- url     : https://prove2.me/submissions/96ca8d26-854a-4f5d-a394-c15965d2eba3

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



/-- The three-pair determinant polynomial remains uniformly small with
the asymmetric first-row/later-row perturbations. -/
theorem _root_.solution (P Q R : ℂ)
    (hP : ‖P - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hQ : ‖Q - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hR : ‖R - (1/4 : ℂ)‖ < (7/192 : ℝ)) :
    ‖P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R)‖ < (3/10 : ℝ) := by
  let a := P - (1/4 : ℂ)
  let b := Q - (1/4 : ℂ)
  let c := R - (1/4 : ℂ)
  have ha : ‖a‖ < (7/192 : ℝ) := hP
  have hb : ‖b‖ < (7/192 : ℝ) := hQ
  have hc : ‖c‖ < (7/192 : ℝ) := hR
  have hsum : ‖a+b+c‖ < (7/64 : ℝ) := by
    have h := norm_add_le (a+b) c
    have h' := norm_add_le a b
    linarith only [h, h', ha, hb, hc]
  have hdiff : ‖a-b-c‖ < (7/64 : ℝ) := by
    have h := norm_sub_le (a-b) c
    have h' := norm_sub_le a b
    linarith only [h, h', ha, hb, hc]
  have hsq : ‖a-b-c‖^2 < (7/64 : ℝ)^2 := by
    have hleft : 0 ≤ ‖a-b-c‖ := norm_nonneg _
    have hfirst :
        ‖a-b-c‖*‖a-b-c‖ ≤ (7/64 : ℝ)*‖a-b-c‖ :=
      mul_le_mul_of_nonneg_right hdiff.le hleft
    have hsecond :
        (7/64 : ℝ)*‖a-b-c‖ < (7/64 : ℝ)*(7/64 : ℝ) :=
      mul_lt_mul_of_pos_left hdiff (by norm_num)
    nlinarith only [hfirst, hsecond]
  have hprod : ‖b‖*‖c‖ < (7/192 : ℝ)^2 := by
    calc
      _ ≤ (7/192 : ℝ)*‖c‖ :=
        mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)
      _ < (7/192 : ℝ)*(7/192 : ℝ) :=
        mul_lt_mul_of_pos_left hc (by norm_num)
      _ = (7/192 : ℝ)^2 := by ring
  have hquadratic : ‖(a-b-c)^2 - (4 : ℂ)*b*c‖ <
      (13 : ℝ)*(7/192)^2 := by
    have hbq :
        ‖(a-b-c)^2 - (4 : ℂ)*b*c‖ ≤
          ‖a-b-c‖^2 + 4*(‖b‖*‖c‖) := by
      calc
        _ ≤ ‖(a-b-c)^2‖ + ‖(4 : ℂ)*b*c‖ := norm_sub_le _ _
        _ = ‖a-b-c‖^2 + 4*(‖b‖*‖c‖) := by
          simp [norm_pow]
          ring
    nlinarith only [hbq, hsq, hprod]
  have hpoly :
      P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R) =
        -(3/16 : ℂ) - (a+b+c)/2 + ((a-b-c)^2 - 4*b*c) := by
    dsimp [a,b,c]
    ring
  rw [hpoly]
  have hnormLinear : ‖(a+b+c)/2‖ = ‖a+b+c‖/2 := by simp
  calc
    ‖-(3/16 : ℂ) - (a+b+c)/2 + ((a-b-c)^2 - 4*b*c)‖
        ≤ ‖-(3/16 : ℂ) - (a+b+c)/2‖ +
          ‖(a-b-c)^2 - 4*b*c‖ := norm_add_le _ _
    _ ≤ ‖-(3/16 : ℂ)‖ + ‖(a+b+c)/2‖ +
          ‖(a-b-c)^2 - 4*b*c‖ := by
        have h := norm_sub_le (-(3/16 : ℂ)) ((a+b+c)/2)
        linarith only [h]
    _ < (3/16 : ℝ) + (7/64)/2 + 13*(7/192)^2 := by
        rw [hnormLinear]
        have hn : ‖-(3/16 : ℂ)‖ = (3/16 : ℝ) := by norm_num
        rw [hn]
        linarith only [hsum, hquadratic]
    _ < 3/10 := by norm_num



end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
