-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.roots_outside_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:09.903311+00:00
-- url     : https://prove2.me/submissions/a599f311-07b8-45bd-bfba-92d33b3c6106

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_roots_outside_jointly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.RootsOutOfParts := fun _ => roots_outside_jointly
end Formalism.FourierDecayAlt.P
