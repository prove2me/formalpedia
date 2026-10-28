-- Prove2me | solution 1 for D1Bound5.four_operator_norm_lt_of_entry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:30.490513+00:00
-- url     : https://prove2.me/submissions/fa7e7576-a51d-43af-a4fd-15e770b92a24

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_four_zero_diagonal_operator_norm_lt

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- In dimension four, the L2 operator norm is bounded by a diagonal
entry bound plus three times an off-diagonal entry bound. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ i, ‖E i i‖ < a)
    (hoff : ∀ i j, i ≠ j → ‖E i j‖ < b) :
    ‖E‖ < a + 3*b := by
  let D : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal (fun i => E i i)
  let U : Matrix (Fin 4) (Fin 4) ℂ := fun i j => if i = j then 0 else E i j
  have hsplit : E = D + U := by
    ext i j
    change E i j = D i j + U i j
    by_cases hij : i = j
    · subst j
      simp [D, U]
    · simp [D, U, hij]
  have hD : ‖D‖ < a := by
    dsimp [D]
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_lt_iff ha).2 hd
  have hUdiag : ∀ i, U i i = 0 := by intro i; simp [U]
  have hUoff : ∀ i j, i ≠ j → ‖U i j‖ < b := by
    intro i j hij
    simpa [U, hij] using hoff i j hij
  have hU := four_zero_diagonal_operator_norm_lt U b hb hUdiag hUoff
  calc
    ‖E‖ = ‖D + U‖ := congrArg norm hsplit
    _ ≤ ‖D‖ + ‖U‖ := norm_add_le _ _
    _ < a + 3*b := by linarith





end D1Bound5


namespace D1Bound5





end D1Bound5

namespace D1Bound5



end D1Bound5
end
