-- Prove2me | solution 1 for D1Bound5.reference_inverse_error_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:35.363982+00:00
-- url     : https://prove2.me/submissions/05d8bdd2-6c19-4a22-ae66-1bfd202331e5

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
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



















/-- The sharp reference inverse norm makes the normalized correction a
strict contraction when all pair products have modulus at least nine. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < 3 * (128/8649 : ℝ)) :
    ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1 := by
  calc
    ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖
        ≤ ‖halfOffDiagonalInverse‖ * ‖F - halfOffDiagonal‖ :=
          Matrix.l2_opNorm_mul _ _
    _ = 2 * ‖F - halfOffDiagonal‖ := by rw [halfOffDiagonalInverse_norm]
    _ < 2 * (3 * (128/8649 : ℝ)) :=
      mul_lt_mul_of_pos_left hnear (by norm_num)
    _ < 1 := by norm_num

end D1Bound5
end
