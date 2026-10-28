-- Prove2me | solution 1 for D1Bound5.productFive_prefix_coordinate_div_lt_eighteenth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:19.050539+00:00
-- url     : https://prove2.me/submissions/2274b8c3-4fe9-4607-852d-d275606f8a2a

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
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5









/-- Ordered last-four-entry growth implies a ratio bound for every prefix coordinate. -/
theorem _root_.solution
    (t : Fin 5 → ℂ)
    (hmon : Monotone (fun i => ‖t i‖))
    (hb : (3 : ℝ) ≤ ‖t 1‖)
    (hlarge : 2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ < ‖t 4‖)
    (i : Fin 4) :
    ‖fivePrefixValues t i / t 4‖ < (1/18 : ℝ) := by
  have hbc : ‖t 1‖ ≤ ‖t 2‖ := hmon (by decide)
  have hc : (3 : ℝ) ≤ ‖t 2‖ := hb.trans hbc
  have hbc9 : (9 : ℝ) ≤ ‖t 1‖ * ‖t 2‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have hs0 : (0 : ℝ) ≤ ‖t 3‖ := norm_nonneg _
  have h18 : (18 : ℝ) * ‖t 3‖ < ‖t 4‖ := by
    have hcoef : (18 : ℝ) ≤ 2 * ‖t 1‖ * ‖t 2‖ := by
      nlinarith only [hbc9]
    have hh := mul_le_mul_of_nonneg_right hcoef hs0
    nlinarith only [hh, hlarge]
  have hlastpos : (0 : ℝ) < ‖t 4‖ := by
    have hx : (0 : ℝ) ≤ 2 * ‖t 1‖ * ‖t 2‖ * ‖t 3‖ := by positivity
    linarith only [hx, hlarge]
  have hindex : ‖t (Fin.castAdd 1 i)‖ ≤ ‖t 3‖ := by
    apply hmon
    fin_cases i <;> decide
  change ‖t (Fin.castAdd 1 i) / t 4‖ < (1/18 : ℝ)
  rw [norm_div]
  apply (div_lt_iff₀ hlastpos).mpr
  linarith only [hindex, h18]

end D1Bound5
end
