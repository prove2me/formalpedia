-- Prove2me | solution 1 for D1Bound5.symmetric_zero_four_det_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:07.872724+00:00
-- url     : https://prove2.me/submissions/7432060c-4bf8-4b02-aed7-854a206bbc39

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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Theorems.Thm_D1Bound5_symmetricZeroFour_det_norm_lt

section
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5



/-- The large-entry determinant bound for any symmetric zero-diagonal
matrix with the six entrywise deviations established in RootMatrixSigns. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hsmall : ∀ i j, i ≠ j →
      ‖F i j - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖F.det‖ < productFourH * productFourS^3 := by
  have hmatrix : F =
      !![0,F 0 1,F 0 2,F 0 3;
         F 0 1,0,F 1 2,F 1 3;
         F 0 2,F 1 2,0,F 2 3;
         F 0 3,F 1 3,F 2 3,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [Matrix.of_apply, hd, hsymm]
    all_goals exact hsymm 1 0
  rw [hmatrix]
  exact symmetricZeroFour_det_norm_lt _ _ _ _ _ _
    (hsmall 0 1 (by decide)) (hsmall 0 2 (by decide))
    (hsmall 0 3 (by decide)) (hsmall 1 2 (by decide))
    (hsmall 1 3 (by decide)) (hsmall 2 3 (by decide))

end D1Bound5

namespace D1Bound5





end D1Bound5
end
