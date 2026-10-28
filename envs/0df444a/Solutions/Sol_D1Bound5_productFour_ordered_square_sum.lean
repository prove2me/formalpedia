-- Prove2me | solution 1 for D1Bound5.productFour_ordered_square_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:50.567507+00:00
-- url     : https://prove2.me/submissions/c2026d3d-7573-4660-8140-48cea3e0594b

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Mathlib.Data.Int.GCD
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

/-- A quantitative square-sum estimate from the already established
irregular-growth inequality. The entries may have equal moduli. -/
theorem _root_.solution
    (A B C D : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hBC : B ≤ C) (hB : 3 ≤ B) (htail : 2*B*C < D) :
    A^2+B^2+C^2+D^2 ≤ (13/12 : ℝ)*D^2 := by
  have hC : 0 ≤ C := by linarith
  have hAC : A ≤ C := le_trans hAB hBC
  have hD6 : 6*C < D := by
    have hm := mul_le_mul_of_nonneg_right hB hC
    nlinarith only [hm, htail]
  have hDpos : 0 < D := by nlinarith only [hD6, hC]
  have hSq : 0 < (D-6*C)*(D+6*C) := by
    apply mul_pos
    · linarith
    · nlinarith only [hDpos, hC]
  have hA2 : A^2 ≤ C^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hAC) (add_nonneg hC hA)]
  have hB2 : B^2 ≤ C^2 := by
    have hBnonneg : 0 ≤ B := by linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr hBC) (add_nonneg hC hBnonneg)]
  nlinarith only [hA2, hB2, hSq]



end D1Bound5

namespace D1Bound5



end D1Bound5
end
