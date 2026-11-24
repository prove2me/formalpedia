-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.rn_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:44.063988+00:00
-- url     : https://prove2.me/submissions/8a667a65-034f-412a-a502-eaa55ade00e7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv_mul

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
theorem _root_.solution (x : RC k j ρ) : (Rn k j ρ x)⁻¹ * Rn k j ρ x = 1 := by
  rw [rn_eq, uni_inv, uni_inv_mul]
end Formalism.FourierDecayAlt.P.Ux3
