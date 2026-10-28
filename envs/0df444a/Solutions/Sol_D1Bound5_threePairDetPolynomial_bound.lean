-- Prove2me | solution 1 for D1Bound5.threePairDetPolynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:42.857982+00:00
-- url     : https://prove2.me/submissions/8412ed80-91cc-44c2-97b0-8a99c3e3e6f1

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



/-- A three-pair polynomial estimate, avoiding singular-value theory. -/
theorem _root_.solution (P Q R : ℂ)
    (hP : ‖P - (1/4 : ℂ)‖ < (1/40 : ℝ))
    (hQ : ‖Q - (1/4 : ℂ)‖ < (1/40 : ℝ))
    (hR : ‖R - (1/4 : ℂ)‖ < (1/40 : ℝ)) :
    ‖P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R)‖ < (6/25 : ℝ) := by
  let a := P - (1/4 : ℂ)
  let b := Q - (1/4 : ℂ)
  let c := R - (1/4 : ℂ)
  have ha : ‖a‖ < (1/40 : ℝ) := hP
  have hb : ‖b‖ < (1/40 : ℝ) := hQ
  have hc : ‖c‖ < (1/40 : ℝ) := hR
  have hsum : ‖a+b+c‖ < (3/40 : ℝ) := by
    have h := norm_add_le (a+b) c
    have h' := norm_add_le a b
    linarith only [h, h', ha, hb, hc]
  have hdiff : ‖a-b-c‖ < (3/40 : ℝ) := by
    have h := norm_sub_le (a-b) c
    have h' := norm_sub_le a b
    linarith only [h, h', ha, hb, hc]
  have hsq : ‖a-b-c‖^2 < (3/40 : ℝ)^2 := by
    have hleft : 0 ≤ ‖a-b-c‖ := norm_nonneg _
    have hfirst :
        ‖a-b-c‖*‖a-b-c‖ ≤ (3/40 : ℝ)*‖a-b-c‖ :=
      mul_le_mul_of_nonneg_right hdiff.le hleft
    have hsecond :
        (3/40 : ℝ)*‖a-b-c‖ < (3/40 : ℝ)*(3/40 : ℝ) :=
      mul_lt_mul_of_pos_left hdiff (by norm_num)
    nlinarith only [hfirst, hsecond]
  have hprod : ‖b‖*‖c‖ < (1/1600 : ℝ) := by
    calc
      _ ≤ (1/40 : ℝ)*‖c‖ :=
        mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)
      _ < (1/40 : ℝ)*(1/40 : ℝ) :=
        mul_lt_mul_of_pos_left hc (by norm_num)
      _ = 1/1600 := by norm_num
  have hquadratic : ‖(a-b-c)^2 - (4 : ℂ)*b*c‖ < (13/1600 : ℝ) := by
    have hbq :
        ‖(a-b-c)^2 - (4 : ℂ)*b*c‖ ≤
        ‖a-b-c‖^2 + 4*(‖b‖*‖c‖) := by
      calc
        _ ≤ ‖(a-b-c)^2‖ + ‖(4 : ℂ)*b*c‖ := norm_sub_le _ _
        _ = ‖a-b-c‖^2 + 4*(‖b‖*‖c‖) := by
          simp [norm_pow]
          ring
    linarith only [hbq, hsq, hprod]
  have hpoly :
      P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R) =
      -(3/16 : ℂ) - (a+b+c)/2 + ((a-b-c)^2 - 4*b*c) := by
    dsimp [a, b, c]
    ring
  rw [hpoly]
  have hnormLinear : ‖(a+b+c)/2‖ = ‖a+b+c‖ / 2 := by
    simp
  calc
    ‖-(3/16 : ℂ) - (a+b+c)/2 + ((a-b-c)^2 - 4*b*c)‖
        ≤ ‖-(3/16 : ℂ) - (a+b+c)/2‖ +
          ‖(a-b-c)^2 - 4*b*c‖ := norm_add_le _ _
    _ ≤ ‖-(3/16 : ℂ)‖ + ‖(a+b+c)/2‖ +
          ‖(a-b-c)^2 - 4*b*c‖ := by
        have h := norm_sub_le (-(3/16 : ℂ)) ((a+b+c)/2)
        linarith only [h]
    _ < (3/16 : ℝ) + (3/40)/2 + 13/1600 := by
        rw [hnormLinear]
        have hn : ‖-(3/16 : ℂ)‖ = (3/16 : ℝ) := by norm_num
        rw [hn]
        linarith only [hsum, hquadratic]
    _ < 6/25 := by norm_num

end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5
end
