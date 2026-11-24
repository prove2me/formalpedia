-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.tz_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:00.699126+00:00
-- url     : https://prove2.me/submissions/07669e4b-585f-4ebb-bf96-f777da755ca3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_column_index_second_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_z_hat_of_block3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_herm_eq_zhat
import Theorems.Thm_Formalism_QuantumDeterminants_Zhat_eq


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
theorem _root_.solution (v : Fin (2 * (j + ρ) + k + 1) → ℂ) (hv : inWb k (j + ρ) v) :
    Tz k (j + ρ) v = Tz k ρ (lowV k j ρ v) := by
  unfold Tz
  rw [herm_eq_zhat, herm_eq_zhat,
    show (1 : Matrix (Fin (2 * (j + ρ) + k + 1)) (Fin (2 * (j + ρ) + k + 1)) ℂ) = blk3 1 0 0 0 1 0 0 0 1 from
      block3_one.symm, z_hat_of_block3 v v hv hv]
  have hl : (Fin.last (j + ρ)) = eC j ρ (Sum.inr (Fin.last ρ)) := by ext; rw [column_index_second_val]; simp
  rw [hl, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂,
    Formalism.QuantumDeterminants.Zhat_eq, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.Ux3
