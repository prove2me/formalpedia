-- Prove2me | solution 1 for D1Bound5.finiteN2FixedPolynomial_symmetry_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:57.281119+00:00
-- url     : https://prove2.me/submissions/336c82bf-628e-41ed-842c-5712f36faf03

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
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_neg

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





theorem finiteHomogeneousTwo_star {tau nu : ℤ}
    (n : ℕ) (v : Fin (n+1) → ℤ) (x y : QuadInt tau nu) :
    finiteHomogeneousTwo n v (star x) (star y) =
      star (finiteHomogeneousTwo n v x y) := by
  simp [finiteHomogeneousTwo,mul_comm,mul_left_comm,mul_assoc]



/-- Evaluation and coefficient norms are invariant under the exact
simultaneous sign/conjugation symmetries used by the finite pair table. -/
theorem _root_.solution {tau nu : ℤ}
    (sgn conj : Bool) (x y : QuadInt tau nu) (i : Fin 3) (j : Fin 2) (ell : Fin 3) :
    (finiteN2FixedPolynomial (smallExtensionSymmetry sgn conj x)
      (smallExtensionSymmetry sgn conj y) i j ell).norm =
      (finiteN2FixedPolynomial x y i j ell).norm := by
  cases sgn <;> cases conj <;> fin_cases ell
  all_goals
    simp [smallExtensionSymmetry,finiteN2FixedPolynomial,finiteHomogeneousTwo_neg,
      finiteHomogeneousTwo_star,QuadraticAlgebra.norm_star,QuadraticAlgebra.norm_neg]







end D1Bound5
end
