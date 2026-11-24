-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.rn_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:44.959368+00:00
-- url     : https://prove2.me/submissions/39dbc0ae-c90b-4ee2-bb5f-cd87443a6de6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_mul_wMat_wMat

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
theorem _root_.solution (x : RC k j ρ) : (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ) := by
  rw [rn_eq, hpkBlocks, block3_conjTranspose, block3_mul, block3_mul]
  congr 1 <;> simp [wMat_conjTranspose, hpk_herm, skewOf_conjTranspose, ← Matrix.mul_assoc, wMat_mul_self, mul_wMat_wMat] <;>
    (ext a b; simp [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply]; ring)
end Formalism.FourierDecayAlt.P.Ux3
