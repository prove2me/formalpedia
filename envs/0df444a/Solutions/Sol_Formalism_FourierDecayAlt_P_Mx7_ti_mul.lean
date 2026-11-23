-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.ti_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:08.545522+00:00
-- url     : https://prove2.me/submissions/e46dfbb3-3ce3-412d-bf10-8d4d0b56f848

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absTi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (a b : ℂ) :
    ti P a * ti P b = ggiA P * ggiA P * kap P fun π => (xC P π a)⁻¹ * (xC P π b)⁻¹ := by
  unfold ti
  have c : Commute (kap P fun π => (xC P π a)⁻¹) (ggiA P) := kap_comm_sc P _ _
  rw [absTi _ _ _ c, kap_mul P _ _ _ (fun π => rfl)]
end Formalism.FourierDecayAlt.P.Mx7
