-- Prove2me | solution 1 for D1Bound5.symmetric_zero_four_adjugate_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:12.463557+00:00
-- url     : https://prove2.me/submissions/bf2a0754-ca07-4110-aa45-1f98a8f1331e

import Lean.Util.CollectAxioms
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
import Definitions.Def_D1Bound5_AdjugateCoverage_Definitions
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Theorems.Thm_D1Bound5_symmetricFour_adjugate_norm_lt

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5









/-- The cofactor estimate holds for any symmetric zero-diagonal complex
matrix, expressed without choosing or labelling its six entries. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hzero : ∀ i, F i i = 0)
    (hsym : ∀ i j, F i j = F j i)
    (hnear : ∀ i j, i ≠ j →
      ‖F i j - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖F.adjugate‖ < productFourH * productFourS^2 := by
  have hrepr : F = symmetricFour (F 0 1) (F 0 2) (F 0 3)
      (F 1 2) (F 1 3) (F 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp (config := {decide := true}) [symmetricFour, hzero] <;>
        (first | exact hsym _ _ | exact (hsym _ _).symm))
  rw [hrepr]
  exact symmetricFour_adjugate_norm_lt
    (F 0 1) (F 0 2) (F 0 3) (F 1 2) (F 1 3) (F 2 3)
    (hnear 0 1 (by decide)) (hnear 0 2 (by decide))
    (hnear 0 3 (by decide)) (hnear 1 2 (by decide))
    (hnear 1 3 (by decide)) (hnear 2 3 (by decide))

end D1Bound5
end
