-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.N_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:16.937806+00:00
-- url     : https://prove2.me/submissions/60407596-0844-44f8-85ac-df50b23c49d4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_abs_Nc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mem_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mem_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_nabla_star_gamma_relations

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
theorem _root_.solution : nabA P * cc P = cc P * nabA P - cc P * cc P :=
  abs_Nc _ _ _ (N_zb P) (nabla_star_gamma_relations P) (fcomm P (mem_G P) (mem_zb P))
end Formalism.FourierDecayAlt.P.Mx6
