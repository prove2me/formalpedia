-- Prove2me | solution 1 for D1Bound5.four_all_entries_operator_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:37.031057+00:00
-- url     : https://prove2.me/submissions/4a49e90f-983f-416a-89e0-5aaf70e1f286

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
import Theorems.Thm_D1Bound5_four_zero_diagonal_operator_norm_lt

section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5

/-- An entrywise estimate for the complex L2 operator norm in dimension four. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ∀ i j, ‖E i j‖ < δ) :
    ‖E‖ < 4 * δ := by
  let D : Matrix (Fin 4) (Fin 4) ℂ := diagonal (fun i => E i i)
  let R : Matrix (Fin 4) (Fin 4) ℂ := E - D
  have hD : ‖D‖ < δ := by
    dsimp [D]
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_lt_iff hδ).2 (fun i => h i i)
  have hdiag : ∀ i, R i i = 0 := by
    intro i
    simp [R, D, Matrix.sub_apply]
  have hoff : ∀ i j, i ≠ j → ‖R i j‖ < δ := by
    intro i j hij
    simpa [R, D, Matrix.sub_apply, Matrix.diagonal_apply, hij] using h i j
  have hR : ‖R‖ < 3 * δ :=
    four_zero_diagonal_operator_norm_lt R δ hδ hdiag hoff
  have hsplit : E = D + R := by
    dsimp [R]
    abel
  calc
    ‖E‖ = ‖D + R‖ := congrArg norm hsplit
    _ ≤ ‖D‖ + ‖R‖ := norm_add_le D R
    _ < δ + 3 * δ := add_lt_add hD hR
    _ = 4 * δ := by ring









end D1Bound5
end
