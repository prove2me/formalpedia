-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.comm_dd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:36.804344+00:00
-- url     : https://prove2.me/submissions/3659fc37-411c-42ba-bbd3-d1a5367f0d4c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_comm
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
theorem _root_.solution (u v : ℂ) : dA P v * dA P u = dA P u * dA P v := by
  simp only [dA, smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, absCC _ _ _ _ rfl (kap_comm P _ _) (kap_G P _) (kap_G P _)]
end Formalism.FourierDecayAlt.P.Mx6
