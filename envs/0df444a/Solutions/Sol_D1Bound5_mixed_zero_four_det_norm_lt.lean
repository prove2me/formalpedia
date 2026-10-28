-- Prove2me | solution 1 for D1Bound5.mixed_zero_four_det_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:48.412948+00:00
-- url     : https://prove2.me/submissions/cf8ac165-9ef2-4894-8d91-16d8dfe3c192

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
import Theorems.Thm_D1Bound5_mixedSymmetricFour_det_lt

section
open Matrix

namespace D1Bound5







end D1Bound5

namespace D1Bound5

/-- The mixed determinant bound in a matrix-independent index interface. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖F.det‖ < (3/10 : ℝ) := by
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
  exact mixedSymmetricFour_det_lt _ _ _ _ _ _
    (hfirst 0 1 (by decide) (Or.inl rfl))
    (hfirst 0 2 (by decide) (Or.inl rfl))
    (hfirst 0 3 (by decide) (Or.inl rfl))
    (hlater 1 2 (by decide) (by decide))
    (hlater 1 3 (by decide) (by decide))
    (hlater 2 3 (by decide) (by decide))

end D1Bound5

namespace D1Bound5



end D1Bound5
end
