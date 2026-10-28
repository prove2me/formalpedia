-- Prove2me | solution 1 for D1Bound5.halfOffDiagonal_adjugate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:54.969791+00:00
-- url     : https://prove2.me/submissions/f6a7d4bc-b78a-4787-96a9-b2861111ad57

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
import Theorems.Thm_D1Bound5_halfOffDiagonal_det
import Theorems.Thm_D1Bound5_inverse_mul_halfOffDiagonal

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5














/-- The adjugate of the reference matrix, expressed through the explicit
inverse without applying Cramer's rule to individual minors. -/
theorem _root_.solution :
    halfOffDiagonal.adjugate = (-3/16 : ℂ) • halfOffDiagonalInverse := by
  calc
    halfOffDiagonal.adjugate =
        (1 : Matrix (Fin 4) (Fin 4) ℂ) * halfOffDiagonal.adjugate := by simp
    _ = (halfOffDiagonalInverse * halfOffDiagonal) * halfOffDiagonal.adjugate := by
      rw [inverse_mul_halfOffDiagonal]
    _ = halfOffDiagonalInverse * (halfOffDiagonal * halfOffDiagonal.adjugate) := by
      rw [Matrix.mul_assoc]
    _ = halfOffDiagonalInverse * (halfOffDiagonal.det • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
      rw [Matrix.mul_adjugate]
    _ = halfOffDiagonal.det • halfOffDiagonalInverse := by
      simp
    _ = (-3/16 : ℂ) • halfOffDiagonalInverse := by
      rw [halfOffDiagonal_det]



end D1Bound5
end
