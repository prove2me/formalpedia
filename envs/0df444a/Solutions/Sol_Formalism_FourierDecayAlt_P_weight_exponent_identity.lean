-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weight_exponent_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:22.643052+00:00
-- url     : https://prove2.me/submissions/6fa58a53-2fe6-4388-aede-bc388ed115af

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.X.WeightExponent :=
  fun k r j s => ⟨by ring, by ring, by ring⟩
end Formalism.FourierDecayAlt.P
