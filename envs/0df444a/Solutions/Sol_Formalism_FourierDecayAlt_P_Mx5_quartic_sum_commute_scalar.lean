-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.quartic_sum_commute_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:44.153305+00:00
-- url     : https://prove2.me/submissions/c7e03423-ddf9-4f4c-9189-55e5a863f677

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ss_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_sss_sc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (Y : ℂ) (w : Pr P.r) : Commute (S4 P Y) (sc P w) := by
  unfold S4
  exact Commute.sum_left _ _ _ fun l _ => Commute.sum_left _ _ _ fun j _ =>
    ((sss_sc P l w).mul_left (ss_sc P j w)).mul_left (kap_sc P _ w)
end Formalism.FourierDecayAlt.P.Mx5
