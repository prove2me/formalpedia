-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.concrete_data_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:43:34.313922+00:00
-- url     : https://prove2.me/submissions/0a8b043d-c7ea-4478-92a0-479cdbcee045

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.MkDataInst := by
  intro E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th e
  unfold J.Inst J.PlacesOf
  exact ⟨rfl, rfl, fun _ _ => rfl, S.hv, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl⟩
end Formalism.FourierDecayAlt.P
