-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.eisenstein_canonical_pair_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:55:23.240448+00:00
-- url     : https://prove2.me/submissions/19f4c8d0-4344-4189-9113-0ee6b41c75ec

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
import Theorems.Thm_D1Bound5_eisenstein_exceptional_pair_extension_trace_zero
import Theorems.Thm_D1Bound5_eisenstein_no_three_trace_zero_extensions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





/-- The exceptional Eisenstein pair excludes three further compatible
entries. Both anchor orientations are handled by exchanging witnesses. -/
theorem _root_.solution
    (t : Fin 6 → QuadInt 1 1) (ht : IsD1Tuple t)
    (hpair : EisensteinCanonicalPair (t 0) (t 1)) : False := by
  have htrace (i : Fin 6) (hi0 : (0 : Fin 6) ≠ i) (hi1 : (1 : Fin 6) ≠ i) :
      2*(t i).re+(t i).im=0 := by
    have h0 := ht.2.2 0 i hi0
    have h1 := ht.2.2 1 i hi1
    rcases hpair with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact eisenstein_exceptional_pair_extension_trace_zero (t i)
        (by simpa only [ha] using h0) (by simpa only [hb] using h1)
    · exact eisenstein_exceptional_pair_extension_trace_zero (t i)
        (by simpa only [ha] using h1) (by simpa only [hb] using h0)
  exact eisenstein_no_three_trace_zero_extensions (t 2) (t 3) (t 4)
    (ht.2.1 2) (ht.2.1 3) (ht.2.1 4)
    (htrace 2 (by decide) (by decide)) (htrace 3 (by decide) (by decide))
    (htrace 4 (by decide) (by decide))
    (ht.2.2 2 3 (by decide)) (ht.2.2 2 4 (by decide)) (ht.2.2 3 4 (by decide))





end D1Bound5
end
