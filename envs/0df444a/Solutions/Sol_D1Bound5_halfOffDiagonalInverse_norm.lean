-- Prove2me | solution 1 for D1Bound5.halfOffDiagonalInverse_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:17.264905+00:00
-- url     : https://prove2.me/submissions/8602e426-f153-4fa5-b90f-df7959c57cf0

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
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm_ge
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm_le

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

















theorem _root_.solution :
    ‖halfOffDiagonalInverse‖ = 2 :=
  le_antisymm halfOffDiagonalInverse_norm_le halfOffDiagonalInverse_norm_ge



end D1Bound5
end
