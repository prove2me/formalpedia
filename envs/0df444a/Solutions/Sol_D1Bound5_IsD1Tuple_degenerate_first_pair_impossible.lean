-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.degenerate_first_pair_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:51:43.924244+00:00
-- url     : https://prove2.me/submissions/0848698d-03be-4af4-8cf2-46b6ff6e67df

import Init
import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
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
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
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
import Definitions.Def_D1Bound5_DegeneratePairClassification_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_coordinate_equiv
import Theorems.Thm_D1Bound5_IsD1Tuple_eisenstein_canonical_pair_impossible
import Theorems.Thm_D1Bound5_IsD1Tuple_rational_unit_pair_impossible
import Theorems.Thm_D1Bound5_IsD1Tuple_simultaneous_neg
import Theorems.Thm_D1Bound5_degenerate_pair_model
import Theorems.Thm_D1Bound5_eisenstein_degenerate_pair
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt









/-- The whole degenerate first-pair case is impossible in any imaginary
quadratic full integer ring. Product minus one first forces norm one;
Gaussian repeated anchors are excluded by injectivity, and the only
nonrational remaining model is treated by actual Eisenstein Pell descent. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hprod : t 0*t 1+1=0) : False := by
  obtain ⟨tau,nu,htau,hd,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  let u : Fin 6 → QuadInt tau nu := fun i => e.symm (t i)
  have hu : IsD1Tuple u := ht.coordinate_equiv t e.symm
  have hne : u 0 ≠ u 1 := fun h => (by decide : (0 : Fin 6) ≠ 1) (hu.1 h)
  have huprod : u 0*u 1+1=0 := by
    simpa only [u,map_mul,map_add,map_one,map_zero] using congrArg e.symm hprod
  have hback (h : RationalUnitPair (u 0) (u 1)) : RationalUnitPair (t 0) (t 1) := by
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · left
      constructor
      · simpa only [u,RingEquiv.apply_symm_apply,map_neg,map_one] using congrArg e ha
      · simpa only [u,RingEquiv.apply_symm_apply,map_one] using congrArg e hb
    · right
      constructor
      · simpa only [u,RingEquiv.apply_symm_apply,map_one] using congrArg e ha
      · simpa only [u,RingEquiv.apply_symm_apply,map_neg,map_one] using congrArg e hb
  rcases degenerate_pair_model htau hd (u 0) (u 1) hne huprod with h | ⟨rfl,rfl⟩
  · exact ht.rational_unit_pair_impossible hK phi t hmon (hback h)
  · rcases eisenstein_degenerate_pair (u 0) (u 1) hne huprod with h | h | h
    · exact ht.rational_unit_pair_impossible hK phi t hmon (hback h)
    · exact hu.eisenstein_canonical_pair_impossible u h
    · exact (hu.simultaneous_neg u).eisenstein_canonical_pair_impossible (fun i => -u i) h

end D1Bound5
end
