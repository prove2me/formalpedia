-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.cornerInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:45.7978+00:00
-- url     : https://prove2.me/submissions/4a7ff773-b8c0-446c-9afe-c7b42de932b9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lower_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowK_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upK_inv

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
theorem _root_.solution : CornerInv := by
  intro p s a b lh uh l u hlh hl huh hu
  rw [lower_iff] at hlh hl
  rw [upper_iff] at huh hu
  obtain ⟨hlhi, -, -⟩ := lowK_inv hlh
  obtain ⟨huhi, -, -⟩ := upK_inv huh
  constructor
  · unfold cornerA
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
      · rw [hlhi.1, mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨0, hps.1⟩]
        · rw [hl.1, one_mul]; rfl
        · intro c _ hc
          have : 0 < c.val := by have : c.val ≠ 0 := fun e => hc (Fin.ext e); omega
          rw [hl.2 ⟨0, hps.1⟩ c (kL_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
        · simp
      · intro c _ hc
        have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
        rw [hlhi.2 c ⟨p - 1, by omega⟩ (kL_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]
  · unfold cornerB
    by_cases hps : 0 < s ∧ 0 < p
    · rw [dif_pos hps, dif_pos hps, Matrix.mul_apply, Finset.sum_eq_single ⟨0, hps.1⟩]
      · rw [hu.1, mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨p - 1, by omega⟩]
        · rw [huhi.1, one_mul]; rfl
        · intro c _ hc
          have : c.val < p - 1 := by have := c.isLt; have : c.val ≠ p - 1 := fun e => hc (Fin.ext e); omega
          rw [huhi.2 ⟨p - 1, by omega⟩ c (kU_lt.mpr (Fin.lt_def.mpr this)), zero_mul]
        · simp
      · intro c _ hc
        have : 0 < c.val := by have : c.val ≠ 0 := fun e => hc (Fin.ext e); omega
        rw [hu.2 c ⟨0, hps.1⟩ (kU_lt.mpr (Fin.lt_def.mpr this)), mul_zero]
      · simp
    · rw [dif_neg hps, dif_neg hps]
end Formalism.FourierDecayAlt.P.Ux2
