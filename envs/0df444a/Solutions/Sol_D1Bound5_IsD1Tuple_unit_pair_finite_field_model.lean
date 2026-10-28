-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.unit_pair_finite_field_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:19.919707+00:00
-- url     : https://prove2.me/submissions/9be92638-d4db-4108-9055-61e1cca3adad

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
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
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_unit_pair_first_extension_lt
import Theorems.Thm_D1Bound5_UnitPairPellDescription_norm_lower
import Theorems.Thm_D1Bound5_full_ring_unit_pair_four_real_model

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The exact finite-field reduction for the exceptional unit pair.
The field range, parity and real Pell alternatives are derived from the
actual sextuple; the retained model supplies the same parameter for all
negative integer-square tests in the later graph certificate. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hm : t 0 = -1) (hp : t 1 = 1)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖)) :
    ∃ M : UnitPairArithmeticModel (𝓞 K),
      7 ≤ M.d ∧ M.d < 10000 ∧ M.d % 8 = 7 ∧
      ∀ i : Fin 4, UnitPairRealDescription M.d (t ⟨i.val+2,by omega⟩) := by
  obtain ⟨M,hmod,hreal⟩ := full_ring_unit_pair_four_real_model hK phi t ht hm hp
  have hsmall := ht.unit_pair_first_extension_lt hK phi t hm hp hmon
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hw : f M.w*f M.w = -(M.d : ℂ) := by
    simpa only [map_mul,map_neg,map_intCast] using congrArg f M.square
  have hPell : UnitPairPellDescription M.d M.w (t 2) := Or.inl (hreal 0)
  have hlower := UnitPairPellDescription.norm_lower M.d (f M.w) (f (t 2))
    M.positive hw (UnitPairPellDescription.map f M.d M.w (t 2) hPell)
  change ‖f (t 2)‖ < 10000 at hsmall
  have hdR : (M.d : ℝ) < 10000 := by linarith only [hlower,hsmall]
  have hdmax : M.d < 10000 := by exact_mod_cast hdR
  have hdmin : 7 ≤ M.d := by have := M.positive; omega
  exact ⟨M,hdmin,hdmax,hmod,hreal⟩

end D1Bound5
end
