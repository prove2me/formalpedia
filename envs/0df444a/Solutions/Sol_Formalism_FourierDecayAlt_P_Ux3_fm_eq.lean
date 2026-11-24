-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.fm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:33.197904+00:00
-- url     : https://prove2.me/submissions/ebf054ba-fd8d-42f3-8b3c-14fe46fd8d77

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_middle_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_last_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_column_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_column_index_second_val
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_ge
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (z : Fin (2 * (j + ρ) + k + 1) → ℂ) (hz : inWb k (j + ρ) z) :
    Formalism.QuantumDeterminants.Fm k (j + ρ) z = Matrix.reindex (eB k j ρ) (eC j ρ) (F0 (Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))) := by
  ext i c
  obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨y, rfl⟩ := (eC j ρ).surjective c
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply, F0]
  rcases x with ((x | x) | x) <;> rcases y with (y | y)
  · rw [fvec_apply_lt z hz _ _ (by rw [block_index_first_val]; omega), block_index_first_val, column_index_first_val]
    simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  · rw [fvec_apply_lt z hz _ _ (by rw [block_index_first_val]; omega), block_index_first_val, column_index_second_val, if_neg (by omega)]
    simp
  · by_cases hlt : j + x.val < j + ρ
    · rw [fvec_apply_lt z hz _ _ (by rw [block_index_middle_val]; omega), block_index_middle_val, column_index_first_val, if_neg (by omega)]
      simp
    · rw [fvec_apply_ge z _ _ (by rw [block_index_middle_val]; omega), column_index_first_val, if_neg (by omega)]
      simp
  · simp only [Matrix.fromRows_apply_inl, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    unfold fvec
    rw [column_index_second_val]
    by_cases hc : y.val < ρ
    · rw [dif_pos (by omega), dif_pos hc]
      simp only [bvec, eI, Pi.single_apply, Fin.ext_iff, block_index_middle_val]
      by_cases hxy : x.val = y.val
      · rw [if_pos (by omega), if_pos hxy]
      · rw [if_neg (by omega), if_neg hxy]
    · rw [dif_neg (by omega), dif_neg hc]
      simp only [lowV]
      congr 1
  · rw [fvec_apply_ge z _ _ (by rw [block_index_last_val]; omega), hz _ (Or.inr (by rw [block_index_last_val]; omega))]
    simp
  · rw [fvec_apply_ge z _ _ (by rw [block_index_last_val]; omega), hz _ (Or.inr (by rw [block_index_last_val]; omega))]
    simp
end Formalism.FourierDecayAlt.P.Ux3
