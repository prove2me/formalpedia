-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.star_t22
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:08.132177+00:00
-- url     : https://prove2.me/submissions/31e99234-0949-44a2-82f5-dd182769e61a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_g__b50cdc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_g__636104
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_xC

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
theorem _root_.solution (u : ℂ) : star (t22 P (star u)) = t22 P u := by
  rw [t22, t22, star_mul, star_g, xA, xA, star_kap, kap_g]
  congr 2
  funext π
  exact star_xC P π u
end Formalism.FourierDecayAlt.P.Mx6
