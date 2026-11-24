-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cutoff_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:00.437748+00:00
-- url     : https://prove2.me/submissions/89049a2d-9f98-4b57-a577-2496ee5a2feb

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
theorem _root_.solution : C.CutoffOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S H _ _ Vt hPG Kr hK0 Th e Y hY
  filter_upwards [hPG Y hY] with ε hε p hp q hq _
  exact hε p hp q hq
end Formalism.FourierDecayAlt.P
