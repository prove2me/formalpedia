-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.concrete_axioms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:14.206658+00:00
-- url     : https://prove2.me/submissions/9b7b1651-1860-4a4a-81d0-2e0d2b5b9844

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
theorem _root_.solution : Formalism.FourierDecayAlt.JC.AxiomsConcrete := by
  intro hAx hLC hA13 E _ _ _ Wp Wq _ _ _ _ S Kr hK0 Th hLM
  exact hAx hLC hA13 E _ (S.mkData Kr hK0 Th fun _ => 0) hLM
end Formalism.FourierDecayAlt.P
