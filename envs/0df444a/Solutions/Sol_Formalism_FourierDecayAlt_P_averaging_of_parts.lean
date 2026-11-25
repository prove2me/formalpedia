-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.averaging_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:25.241948+00:00
-- url     : https://prove2.me/submissions/d375aaf7-98cc-44dd-a9b2-94d16d50e611

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes
import Theorems.Thm_Formalism_FourierDecayAlt_P_averaging_vanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open GeometricRayBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.AveragingOfParts := fun _ => averaging_vanishes
end Formalism.FourierDecayAlt.P
