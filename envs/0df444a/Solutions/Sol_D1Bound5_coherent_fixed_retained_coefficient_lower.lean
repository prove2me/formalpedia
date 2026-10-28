-- Prove2me | solution 1 for D1Bound5.coherent_fixed_retained_coefficient_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:13.615218+00:00
-- url     : https://prove2.me/submissions/f39ac0e3-8a57-4269-9070-b73942934939

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



/-- An upper enclosure for the normalized Vandermonde gives the
conservative fixed-triple coefficient used in the cutoff table. -/
theorem _root_.solution
    (A B R q : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hR : 0 < R)
    (hq : R ≤ q) (hsep : (51051/400000 : ℝ)/B^2 < 1/q) :
    (9999/100 : ℝ)*A^2*(1/q-(51051/400000 : ℝ)/B^2)^2 ≤
      (9999/100 : ℝ)*A^2*(1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
  have hq0 : 0 < q := hR.trans_le hq
  have hA2 : 1 ≤ A^2 := by nlinarith only [hA]
  have hden : B^2 ≤ A^2*B^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hA2) (sq_nonneg B)]
  have hrecip : 1/q ≤ 1/R := one_div_le_one_div_of_le hR hq
  have herr : (51051/400000 : ℝ)/(A^2*B^2) ≤ (51051/400000 : ℝ)/B^2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hB) hden
  have hdelta : 1/q-(51051/400000 : ℝ)/B^2 ≤
      1/R-(51051/400000 : ℝ)/(A^2*B^2) := by linarith only [hrecip,herr]
  have hsquare : (1/q-(51051/400000 : ℝ)/B^2)^2 ≤
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
    exact (sq_le_sq₀ (sub_pos.mpr hsep).le
      ((sub_pos.mpr hsep).trans_le hdelta).le).2 hdelta
  exact mul_le_mul_of_nonneg_left hsquare (by positivity)



end D1Bound5
end
