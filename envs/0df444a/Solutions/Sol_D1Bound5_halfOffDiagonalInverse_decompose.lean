-- Prove2me | solution 1 for D1Bound5.halfOffDiagonalInverse_decompose
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:15.862983+00:00
-- url     : https://prove2.me/submissions/f89af671-18fd-4668-bf6e-ba67f9ce4cf9

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5









theorem _root_.solution :
    halfOffDiagonalInverse =
      (-2/3 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
      (-4/3 : ℂ) • referenceReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [halfOffDiagonalInverse, referenceReflection,
      Matrix.smul_apply] <;> norm_num











end D1Bound5
end
