-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.zhSlice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:30:41.468901+00:00
-- url     : https://prove2.me/submissions/34aabe44-7b2b-4437-b0b3-c9b60d649c62

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hat_z_of_block3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq

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
theorem _root_.solution : ZhSlice := by
  intro k j ρ x x' Z γ
  rw [rn_eq, rn_eq, uni_inv]
  simp only [mMap]
  rw [block3_mul, block3_mul, hat_z_of_block3]
  simp [← Matrix.mul_assoc, wMat_mul_self]
end Formalism.FourierDecayAlt.P.Ux3
