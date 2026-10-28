-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.one_small_reduced_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:56:14.348789+00:00
-- url     : https://prove2.me/submissions/5c8a9e7e-c309-42b7-8871-fb66a9cf4998

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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_not_rational_one_three_eight
import Theorems.Thm_D1Bound5_IsD1Tuple_one_small_first_triple_classification
import Theorems.Thm_D1Bound5_IsD1Tuple_one_small_normalized_rows_impossible
import Theorems.Thm_D1Bound5_IsD1Tuple_one_small_reduced_third_lt_fifteen
import Theorems.Thm_D1Bound5_IsD1Tuple_rational_first_pair_third_eq_eight
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The entire finite first-pair remainder is impossible. This actual
full-ring theorem joins the complete first-pair/third-entry classification,
the analytic S<15 bound, all56 finite fourth complements and the universal
signed rational triple. Only the two remaining first-pair size cases occur
as hypotheses; there are no interval or table-certificate premises. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hsize :
      (‖phi (a 0 : K)‖^2=1 ∧ 9≤‖phi (a 1 : K)‖^2 ∧ ‖phi (a 1 : K)‖^2<64) ∨
      (‖phi (a 0 : K)‖^2=2 ∧ 9≤‖phi (a 1 : K)‖^2 ∧ ‖phi (a 1 : K)‖^2<16)) : False := by
  have hS15 := IsD1Tuple.one_small_reduced_third_lt_fifteen hK phi a ha hmon hsize
  let ii : Fin 3 → Fin 6 := ![0,1,2]
  let t : Fin 3 → 𝓞 K := fun i => a (ii i)
  have hi : Function.Injective ii := by decide
  have ht : IsD1Tuple t :=
    ⟨ha.1.comp hi,fun j => ha.2.1 _,fun j k hjk => ha.2.2 _ _ (hi.ne hjk)⟩
  have hbound : ‖phi (a 2 : K)‖^2 < 225 := by
    nlinarith only [hS15,norm_nonneg (phi (a 2 : K))]
  have horder : ‖phi (a 1 : K)‖^2 ≤ ‖phi (a 2 : K)‖^2 := by
    gcongr
    exact hmon (by decide : (1 : Fin 6) ≤ 2)
  obtain h | h | ⟨tau,nu,e,hmodel,hrows⟩ :=
    IsD1Tuple.one_small_first_triple_classification hK phi t ht hsize hbound horder
  · have h0 : a 0 = if false then -1 else 1 := by simpa [t,ii] using h.1
    have h1 : a 1 = if false then -3 else 3 := by simpa [t,ii] using h.2
    have h2 := IsD1Tuple.rational_first_pair_third_eq_eight hK phi a ha hmon false h0 h1
    exact IsD1Tuple.not_rational_one_three_eight hK phi a ha hmon false h0 h1 h2
  · have h0 : a 0 = if true then -1 else 1 := by simpa [t,ii] using h.1
    have h1 : a 1 = if true then -3 else 3 := by simpa [t,ii] using h.2
    have h2 := IsD1Tuple.rational_first_pair_third_eq_eight hK phi a ha hmon true h0 h1
    exact IsD1Tuple.not_rational_one_three_eight hK phi a ha hmon true h0 h1 h2
  · exact IsD1Tuple.one_small_normalized_rows_impossible hK phi a ha hmon e hrows

end D1Bound5
end
