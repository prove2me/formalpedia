-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.productFour_mixed_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:03.629784+00:00
-- url     : https://prove2.me/submissions/d222d7b1-1dad-4116-8126-1ba5254c16b4

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_exists_symmetric_root_matrix
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth
import Theorems.Thm_D1Bound5_full_ring_productFour_mixed_growth

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5















/-- The mixed growth bound for an actual ordered D(1) quadruple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hA : 1 ≤ ‖phi (t 0 : K)‖)
    (hB : 3 ≤ ‖phi (t 1 : K)‖) :
    (3/2 : ℝ)*‖phi (t 0 : K)‖*‖phi (t 1 : K)‖*
      ‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by
  obtain ⟨M, hdiag, hsymm, hroot⟩ := ht.exists_symmetric_root_matrix t
  have htail := (ht.tail_irregular_and_growth hK phi t hmon hB).2
  exact full_ring_productFour_mixed_growth hK phi t M hdiag hsymm
    hroot hmon hA hB htail

end D1Bound5
end
