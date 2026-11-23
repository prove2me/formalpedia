-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.N_cz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:16.951804+00:00
-- url     : https://prove2.me/submissions/6f89236b-83b3-4abf-9121-38a1ed7baa96

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_abs_Ncz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_g_def
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_besselUnipotent_mulVec_middle_vec
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
theorem _root_.solution : nabA P * cz P = cz P * nabA P - (P.TT : ℂ) • (ggiA P * ggiA P) :=
  abs_Ncz _ _ _ _ _ _ (g_def P) (gG P) (besselUnipotent_mulVec_middle_vec P) (nabla_star_gamma_relations P)
end Formalism.FourierDecayAlt.P.Mx6
