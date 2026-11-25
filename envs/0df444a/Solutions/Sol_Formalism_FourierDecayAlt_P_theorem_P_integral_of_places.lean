-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theorem_P_integral_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:49:10.798109+00:00
-- url     : https://prove2.me/submissions/414557ae-4243-4637-ae7f-659d30cda7f6

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_thmPInt_of_covolume_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.ThmPIntOfPlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S dl hpos hprod hcov hpl
  exact JCx1.needs.thmPInt_of_covolume_prod E Wp Wq S dl hpos hcov hprod hpl
end Formalism.FourierDecayAlt.P
