-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.charBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:16:00.560187+00:00
-- url     : https://prove2.me/submissions/5334e563-2756-4602-aaf6-cbf37cc2d62d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lower_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_symmetricScalarBlockMatrix_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_symmetricScalarBlockMatrix_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_supS_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_subdiagonal_sum_block2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p s : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : CharBlock := by
  intro p s a b lh uh l u hlh hl huh hu
  rw [lower_iff] at hlh hl
  rw [upper_iff] at huh hu
  constructor
  · rw [symmetricScalarBlockMatrix_mul, subdiagonal_sum_block2]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    congr 2
    unfold cornerA
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [hlh.1, mul_one]; rfl
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [hlh.2 c ⟨p - 1, by omega⟩ (kL_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]
  · rw [symmetricScalarBlockMatrix_mul, supS_eq, supS_eq, supS_eq]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
    rw [symmetricScalarBlockMatrix_transpose, subdiagonal_sum_block2]
    congr 2
    unfold cornerB
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, transpose_apply, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [huh.1, one_mul]; rfl
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [huh.2 ⟨p - 1, by omega⟩ c (kU_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
      · simp
    · rw [dif_neg hps, dif_neg hps]
end Formalism.FourierDecayAlt.P.Ux2
