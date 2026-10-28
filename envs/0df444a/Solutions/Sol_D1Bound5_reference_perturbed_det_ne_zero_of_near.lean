-- Prove2me | solution 1 for D1Bound5.reference_perturbed_det_ne_zero_of_near
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:24:35.665542+00:00
-- url     : https://prove2.me/submissions/986b1ba8-4fde-4630-a032-46f4c1495563

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_reference_inverse_error_norm_lt_one
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





/-- The reference estimate makes the normalised 4-by-4 correction invertible. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < 3 * (128/8649 : ℝ)) :
    F.det ≠ 0 :=
  reference_perturbed_det_ne_zero F (reference_inverse_error_norm_lt_one F hnear)





end D1Bound5
end
