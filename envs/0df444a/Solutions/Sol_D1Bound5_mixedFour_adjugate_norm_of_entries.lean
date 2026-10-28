-- Prove2me | solution 1 for D1Bound5.mixedFour_adjugate_norm_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:28.211995+00:00
-- url     : https://prove2.me/submissions/6b74efb2-54f9-4728-b29b-4a7ac7209603

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_MixedAdjugateEnvelope_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate
import Theorems.Thm_D1Bound5_mixedAdjEnvelope_symmetric
import Theorems.Thm_D1Bound5_weightedSchur_four_opNorm

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



theorem mixedAdjEnvelope_nonneg (i j : Fin 4) :
    0 ≤ mixedAdjEnvelope i j := by
  unfold mixedAdjEnvelope
  split_ifs <;> norm_num



theorem mixedAdjEnvelope_rows (i : Fin 4) :
    (∑ j : Fin 4, mixedAdjEnvelope i j * (1 : ℝ)) ≤
      (217/1000 : ℝ) * 1 := by
  fin_cases i <;>
    (norm_num [Fin.sum_univ_four, mixedAdjEnvelope] <;>
      simp <;> norm_num)

/-- Weighted Schur closure for all 16 distinct mixed adjugate entries. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, ‖(F.adjugate - halfOffDiagonal.adjugate) i i‖ <
      if i = 0 then (1/40 : ℝ) else 7/100)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ < (53/1000 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ < (47/1000 : ℝ)) :
    ‖F.adjugate‖ < (155/96 : ℝ) * (59/96)^2 := by
  let E : Matrix (Fin 4) (Fin 4) ℂ :=
    F.adjugate - halfOffDiagonal.adjugate
  have hEb : ∀ i j, ‖E i j‖ ≤ mixedAdjEnvelope i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [E, mixedAdjEnvelope] using le_of_lt (hdiag i)
    · by_cases hz : i = 0 ∨ j = 0
      · simpa [E, mixedAdjEnvelope, hij, hz] using
          le_of_lt (hfirst i j hij hz)
      · simpa [E, mixedAdjEnvelope, hij, hz] using
          le_of_lt (hlater i j hij hz)
  have hw : ∀ i : Fin 4, (0 : ℝ) < (1 : ℝ) := by
    intro i
    norm_num
  have hnorm : ‖E‖ ≤ (217/1000 : ℝ) :=
    weightedSchur_four_opNorm E mixedAdjEnvelope (fun _ => (1 : ℝ))
      (217/1000) mixedAdjEnvelope_nonneg hw
      (by norm_num) mixedAdjEnvelope_symmetric mixedAdjEnvelope_rows hEb
  have href : ‖halfOffDiagonal.adjugate‖ = (3/8 : ℝ) := by
    rw [halfOffDiagonal_adjugate, norm_smul, halfOffDiagonalInverse_norm]
    norm_num
  have hdecomp : F.adjugate =
      halfOffDiagonal.adjugate + E := by
    dsimp [E]
    abel
  calc
    ‖F.adjugate‖ =
        ‖halfOffDiagonal.adjugate + E‖ := congrArg norm hdecomp
    _ ≤ ‖halfOffDiagonal.adjugate‖ + ‖E‖ := norm_add_le _ _
    _ ≤ (3/8 : ℝ) + 217/1000 := by
      rw [href]
      linarith only [hnorm]
    _ < (155/96 : ℝ) * (59/96)^2 := by norm_num

end D1Bound5
end
