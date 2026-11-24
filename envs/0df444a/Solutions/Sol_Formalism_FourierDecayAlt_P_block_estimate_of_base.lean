-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.block_estimate_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:42:14.048024+00:00
-- url     : https://prove2.me/submissions/e651a088-9391-48b9-8d59-9b0c06663eaf

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
theorem _root_.solution : C.EstBlockOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S C₄ h Kr hK0 Th e
  exact h
end Formalism.FourierDecayAlt.P
