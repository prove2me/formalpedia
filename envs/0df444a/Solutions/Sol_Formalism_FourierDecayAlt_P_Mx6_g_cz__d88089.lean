-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.g_cz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:36.436743+00:00
-- url     : https://prove2.me/submissions/5ed78ee6-3a0d-4f5e-8102-c561a2fa39e4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_zeta_mem_function_algebra
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mem_g__96e78a
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG

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
theorem _root_.solution : ggA P * cz P = zA P := by
  unfold cz; rw [lc (fcomm P (mem_g P) (zeta_mem_function_algebra P)), gG, mul_one]
end Formalism.FourierDecayAlt.P.Mx6
