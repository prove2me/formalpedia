-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.first_pair_third_lt_fifteen_of_table
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:23.329826+00:00
-- url     : https://prove2.me/submissions/6a6171bf-029d-4da7-a4a7-f89419c9e925

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_first_pair_third_lt_fifteen_of_fixed
import Theorems.Thm_D1Bound5_firstPairCoordinates_eq
import Theorems.Thm_D1Bound5_firstPairGeometryRows_have_fixed_row
import Theorems.Thm_D1Bound5_firstPairTable_geometry_normalize

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Actual S<15 for every nonrational first pair in the complete finite
classification. Exact row selection and every analytic bound are internal. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K)
    (hmodel : (tau,nu) ∈ smallPairModels)
    (hrow : firstPairCoordinates (e.symm (a 0)) (e.symm (a 1)) ∈ firstPairTable tau nu) :
    ‖phi (a 2 : K)‖ < 15 := by
  obtain ⟨g,hg,hgt,hgn,sgn,conj,hcoords⟩ :=
    firstPairTable_geometry_normalize hmodel (e.symm (a 0)) (e.symm (a 1)) hrow
  obtain ⟨r,hr,hmatch⟩ := firstPairGeometryRows_have_fixed_row g hg
  have hrt : r.triple.tau=tau := hmatch.1.symm.trans hgt
  have hrn : r.triple.nu=nu := hmatch.2.1.symm.trans hgn
  subst hrt
  subst hrn
  have hpair : firstPairCoordinates
      (smallExtensionSymmetry sgn conj (e.symm (a 0)))
      (smallExtensionSymmetry sgn conj (e.symm (a 1))) =
        firstPairCoordinates r.triple.anchorA r.triple.anchorB := by
    rw [hcoords]
    simp only [firstPairCoordinates,OneSmallTripleRow.anchorA,OneSmallTripleRow.anchorB]
    exact Prod.ext hmatch.2.2.1 hmatch.2.2.2.1
  obtain ⟨h0,h1⟩ := firstPairCoordinates_eq _ _ _ _ hpair
  exact IsD1Tuple.first_pair_third_lt_fifteen_of_fixed hK phi a ha hmon
    g hg r hr hmatch e sgn conj h0 h1

end D1Bound5
end
