-- Prove2me | solution 1 for D1Bound5.halfOffDiagonal_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:46:10.795978+00:00
-- url     : https://prove2.me/submissions/0fbab5bb-3b5c-4a29-878b-c40c7a6e9887

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5












/-- Exact reference determinant, obtained from the rank-one determinant
lemma rather than a computer expansion of twenty-four permutation terms. -/
theorem _root_.solution : halfOffDiagonal.det = (-3/16 : ℂ) := by
  let V : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 : Matrix (Fin 4) (Fin 4) ℂ) +
      Matrix.replicateCol (Fin 1) negativeOnes *
        Matrix.replicateRow (Fin 1) positiveOnes
  have hV : halfOffDiagonal = (-1/2 : ℂ) • V := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [V, halfOffDiagonal, negativeOnes,
        positiveOnes, Matrix.mul_apply] <;> norm_num
  have hdot : positiveOnes ⬝ᵥ negativeOnes = (-4 : ℂ) := by
    norm_num [dotProduct, positiveOnes, negativeOnes,
      Fin.sum_univ_succ]
  rw [hV, Matrix.det_smul]
  have hrank : V.det = 1 + positiveOnes ⬝ᵥ negativeOnes := by
    exact Matrix.det_one_add_replicateCol_mul_replicateRow negativeOnes positiveOnes
  rw [hrank, hdot]
  norm_num





end D1Bound5
end
