-- Prove2me | solution 1 for D1Bound5.halfOffDiagonal_adjugate_apply
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:37:51.65409+00:00
-- url     : https://prove2.me/submissions/585e43af-32e3-44c7-8f9f-1512355902b7

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
import Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5
















/-- Exact cofactors at the reference matrix: diagonal 1/4, otherwise -1/8. -/
theorem _root_.solution (i j : Fin 4) :
    halfOffDiagonal.adjugate i j =
      if i = j then (1/4 : ℂ) else (-1/8 : ℂ) := by
  rw [halfOffDiagonal_adjugate]
  by_cases h : i = j
  · simp [halfOffDiagonalInverse, h]
    norm_num
  · simp [halfOffDiagonalInverse, h]
    norm_num

end D1Bound5
end
