-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibre_expansion_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:09.335578+00:00
-- url     : https://prove2.me/submissions/79ede4ec-55e8-423b-9dd0-b6e7ce4c76e5

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
theorem _root_.solution : C6.FibExpText := by
  intro r i hi; nlinarith
end Formalism.FourierDecayAlt.P
