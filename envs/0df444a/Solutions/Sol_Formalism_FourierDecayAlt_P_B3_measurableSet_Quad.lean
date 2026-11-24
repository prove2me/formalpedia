-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.measurableSet_Quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:30:06.850664+00:00
-- url     : https://prove2.me/submissions/b9c4b4db-4af2-4f3c-813e-05e2ba338675

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution : MeasurableSet Quad := by
  unfold Quad
  exact measurableSet_Ioi.prod measurableSet_Ioi
end Formalism.FourierDecayAlt.P.B3
