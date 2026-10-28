-- Prove2me | solution 1 for D1Bound5.finiteA5_rational_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:27.981477+00:00
-- url     : https://prove2.me/submissions/ff1c13b3-090d-41ff-be5e-bd27a2d45a6e

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
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
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Definitions.Def_D1Bound5_OneSmallA5FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteA5RootCoeff_rational_norm_sq
import Theorems.Thm_D1Bound5_finiteA5_fixed_height_of_norm_sq
import Theorems.Thm_D1Bound5_rationalCutoff_b0

section
open scoped NumberField

namespace D1Bound5
open QuadInt






















/-- Actual A5 height at the signed rational pair, valid in every
number field. The coefficient certificate is checked before transfer. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (sgn : Bool) (x y c : 𝓞 K)
    (hx : x = if sgn then -1 else 1)
    (hy : y = if sgn then -3 else 3)
    (hC : 1000 ≤ ‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA5Left (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖+
      ‖finiteA5Right (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖) <
      (oneSmallCutoffRow_56.M5 : ℝ)*‖phi (y : K)‖^12*‖phi (c : K)‖^5 := by
  have hY : ‖phi (y : K)‖ = 3 := by
    rw [hy]
    cases sgn <;> norm_num [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat]
  have hy0 : phi (y : K) ≠ 0 := norm_pos_iff.mp (by rw [hY]; norm_num)
  have hnorm (i : Fin 3) (j : Fin 2) (ell : Fin 6) :
      ‖finiteA5RootCoeff (phi (x : K)) (phi (y : K)) i j ell‖^2 =
        ((finiteA5RootCoeff oneSmallCutoffRow_56.triple.anchorA
          oneSmallCutoffRow_56.triple.anchorB i j ell).norm : ℝ) := by
    change _ =
      ((finiteA5RootCoeff (1 : QuadInt 0 1) (3 : QuadInt 0 1) i j ell).norm : ℝ)
    simpa only [Int.cast_one,Int.cast_ofNat] using
      finiteA5RootCoeff_rational_norm_sq phi 0 1 1 3 sgn x y
        (by simpa only [Int.cast_one,Int.cast_ofNat] using hx)
        (by simpa only [Int.cast_one,Int.cast_ofNat] using hy) i j ell
  have hYsq : ‖phi (y : K)‖^2 =
      (oneSmallCutoffRow_56.triple.anchorB.norm : ℝ) := by
    have hh : ‖phi (y : K)‖^2 = (oneSmallCutoffRow_56.b0 : ℝ) := by
      rw [hY,rationalCutoff_b0]
      norm_num
    simpa only [OneSmallCutoffRow.b0,Rat.cast_intCast] using hh
  exact finiteA5_fixed_height_of_norm_sq oneSmallCutoffRow_56.triple.anchorA
    oneSmallCutoffRow_56.triple.anchorB oneSmallCutoffRow_56.M5
    finiteA5CutoffWeights_56 finiteA5CutoffWeights_56_valid
    (phi (x : K)) (phi (y : K)) (phi (c : K)) hYsq hnorm hy0 hC hCY i

end D1Bound5
end
