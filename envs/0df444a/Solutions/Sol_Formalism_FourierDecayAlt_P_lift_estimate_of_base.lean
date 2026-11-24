-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_estimate_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:05.163619+00:00
-- url     : https://prove2.me/submissions/b4da78b5-e6fe-454c-b6e2-0da4997281d9

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.EstLiftOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S h Kr hK0 Th e
  exact h
end Formalism.FourierDecayAlt.P
