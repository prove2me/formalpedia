-- Prove2me | solution 1 for D1Bound5.coherent_retained_h48_coefficient_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:53.327722+00:00
-- url     : https://prove2.me/submissions/beca5fd0-4897-456f-ac22-52f3aa5c299f

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
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

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The H48 retained coefficient is strictly larger than one throughout
the no-small-entry range. -/
theorem _root_.solution
    (A B R : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hR : 0 < R) (hR8 : R ≤ 8) :
    1 < ((9999/10000 : ℝ)*(200/19)^2)*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
  have hAB : (81 : ℝ) ≤ A^2*B^2 := by
    calc
      (81 : ℝ) = 3^2*3^2 := by norm_num
      _ ≤ A^2*B^2 := by gcongr <;> first | assumption | norm_num
  have hAB0 : 0 < A^2*B^2 := lt_of_lt_of_le (by norm_num) hAB
  have hinv : (1/8 : ℝ) ≤ 1/R := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hR).2
    simpa using hR8
  have herr : (51051/400000 : ℝ)/(A^2*B^2) ≤ (51051/400000)/81 := by
    apply (div_le_div_iff₀ hAB0 (by norm_num : (0 : ℝ) < 81)).2
    nlinarith only [hAB]
  have hd : (1/10 : ℝ) < 1/R-(51051/400000 : ℝ)/(A^2*B^2) := by
    linarith only [hinv, herr]
  have hs : (1/10 : ℝ)^2 < (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2 := by
    have hp := mul_pos (sub_pos.mpr hd)
      (show 0 < (1/R-(51051/400000 : ℝ)/(A^2*B^2))+(1/10) by linarith only [hd])
    nlinarith only [hp]
  nlinarith only [hs]





end D1Bound5
end
