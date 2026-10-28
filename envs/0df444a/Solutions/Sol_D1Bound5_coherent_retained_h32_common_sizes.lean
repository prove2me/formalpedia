-- Prove2me | solution 1 for D1Bound5.coherent_retained_h32_common_sizes
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:23.521975+00:00
-- url     : https://prove2.me/submissions/56dad98d-b49e-4bf7-be20-4d3d053f4b61

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

/-- The mixed retained power gap with AT≥32 supplies the common large
terminal hypotheses for the approximation constructions. -/
theorem _root_.solution
    (A S T C : ℝ) (hA : 1 ≤ A) (hS3 : 3 ≤ S) (hST : S ≤ T)
    (hAT32 : 32 ≤ A*T) (hgap : A^2*T^5/S^2 < C) :
    1000 < C ∧ 200*S < C ∧ 4*T < C := by
  have hS : 0 < S := by linarith only [hS3]
  have hT : 0 < T := hS.trans_le hST
  have hbase : A^2*T^3 ≤ A^2*T^5/S^2 := by
    apply (le_div_iff₀ (pow_pos hS 2)).2
    have hs : S^2 ≤ T^2 := by gcongr
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ A^2*T^3)
    nlinarith only [hh]
  have hT3 : A^2*T^3 < C := hbase.trans_lt hgap
  have hAT2 : (1024 : ℝ) ≤ A^2*T^2 := by nlinarith only [hAT32,sq_nonneg (A*T-32)]
  have hmul := mul_le_mul_of_nonneg_right hAT2 hT.le
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hS3,hST,hmul,hT3]
  · nlinarith only [hST,hS,hmul,hT3]
  · nlinarith only [hT,hmul,hT3]






end D1Bound5
end
