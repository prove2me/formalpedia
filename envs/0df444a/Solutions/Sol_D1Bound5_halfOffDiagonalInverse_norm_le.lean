-- Prove2me | solution 1 for D1Bound5.halfOffDiagonalInverse_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:34.724914+00:00
-- url     : https://prove2.me/submissions/5bfbccf2-a99a-4fb3-adf9-b5dd061baf0b

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
import Definitions.Def_D1Bound5_ReferenceInverseNorm_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_decompose
import Theorems.Thm_D1Bound5_referenceReflection_conjTranspose
import Theorems.Thm_D1Bound5_referenceReflection_sq

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







theorem referenceReflection_norm : ‖referenceReflection‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self referenceReflection
  rw [referenceReflection_conjTranspose, referenceReflection_sq, norm_one] at h
  nlinarith [norm_nonneg referenceReflection]



theorem _root_.solution :
    ‖halfOffDiagonalInverse‖ ≤ 2 := by
  rw [halfOffDiagonalInverse_decompose]
  calc
    ‖(-2/3 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
      (-4/3 : ℂ) • referenceReflection‖
        ≤ ‖(-2/3 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖ +
          ‖(-4/3 : ℂ) • referenceReflection‖ := norm_add_le _ _
    _ = (2/3 : ℝ) * ‖(1 : Matrix (Fin 4) (Fin 4) ℂ)‖ +
          (4/3 : ℝ) * ‖referenceReflection‖ := by
      rw [norm_smul, norm_smul]
      norm_num
    _ = 2 := by rw [norm_one, referenceReflection_norm]; norm_num









end D1Bound5
end
