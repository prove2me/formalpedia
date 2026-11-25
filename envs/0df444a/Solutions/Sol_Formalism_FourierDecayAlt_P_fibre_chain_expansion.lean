-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibre_chain_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:12.966259+00:00
-- url     : https://prove2.me/submissions/a8de0d27-6379-4b5d-a735-e7ea2627ee45

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FibreExpansionZeroFails

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
theorem _root_.solution : C6.FibChainExp := by
  intro r i a _ hai; nlinarith
end Formalism.FourierDecayAlt.P
