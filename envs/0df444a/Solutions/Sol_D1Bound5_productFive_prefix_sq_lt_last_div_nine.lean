-- Prove2me | solution 1 for D1Bound5.productFive_prefix_sq_lt_last_div_nine
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:00.05571+00:00
-- url     : https://prove2.me/submissions/d5a8c035-85c2-436a-96f7-1f1eddff8c08

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix
open scoped NumberField

namespace D1Bound5

/-- The first four ordered moduli are quadratically small relative to
the last one once the product-four growth bound applies. -/
theorem _root_.solution
    (a b c s d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcs : c ≤ s)
    (hb : 3 ≤ b) (hlarge : 2*b*c*s < d) :
    a^2 + b^2 + c^2 + s^2 < (d/9)^2 := by
  have hc : 3 ≤ c := le_trans hb hbc
  have hs : 0 ≤ s := le_trans (by norm_num : (0:ℝ) ≤ 3) (le_trans hc hcs)
  have hb0 : 0 ≤ b := le_trans (by norm_num : (0:ℝ) ≤ 3) hb
  have hc0 : 0 ≤ c := le_trans (by norm_num : (0:ℝ) ≤ 3) hc
  have has : a ≤ s := hab.trans (hbc.trans hcs)
  have hbs : b ≤ s := hbc.trans hcs
  have hasq : a^2 ≤ s^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr has) (add_nonneg ha hs)]
  have hbsq : b^2 ≤ s^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hbs) (add_nonneg hb0 hs)]
  have hcsq : c^2 ≤ s^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg hc0 hs)]
  have hbc9 : (9:ℝ) ≤ b*c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have h18 : 18*s < d := by
    have he : 18*s ≤ (2*b*c)*s :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hbc9]) hs
    nlinarith only [he,hlarge]
  have htwo : 2*s < d/9 := by linarith only [h18]
  have hpositive : 0 < d/9 + 2*s := by linarith only [htwo, hs]
  have hsq : (2*s)^2 < (d/9)^2 := by
    have hprod := mul_pos (sub_pos.mpr htwo) hpositive
    nlinarith only [hprod]
  nlinarith only [hasq, hbsq, hcsq, hsq]



end D1Bound5

namespace D1Bound5



end D1Bound5
end
