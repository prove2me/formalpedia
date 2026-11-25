-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fibre_expansion_zero_fails
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:42.912231+00:00
-- url     : https://prove2.me/submissions/7c829f12-82dd-4880-acfc-67c79524e326

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
theorem _root_.solution : C6.FibExpZeroFails := by
  intro h; have := h 0 0; norm_num at this
end Formalism.FourierDecayAlt.P
