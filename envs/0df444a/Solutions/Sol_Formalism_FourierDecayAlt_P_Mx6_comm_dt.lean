-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.comm_dt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:36.179154+00:00
-- url     : https://prove2.me/submissions/121c6615-14cb-43c9-bea3-a16932d1a6e6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Gg__2bb78f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_g__636104
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_absCC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (u v : ℂ) : dA P v * t22 P u = t22 P u * dA P v := by
  simp only [dA, t22, xA, smul_mul_assoc, mul_smul_comm]
  rw [absCC _ _ _ _ ((Gg P).trans (gG P).symm) (kap_comm P _ _) (kap_g P _) (kap_G P _)]
end Formalism.FourierDecayAlt.P.Mx6
