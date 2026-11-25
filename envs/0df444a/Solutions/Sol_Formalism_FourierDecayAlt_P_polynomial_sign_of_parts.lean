-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.polynomial_sign_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:49.64455+00:00
-- url     : https://prove2.me/submissions/331cccf1-98db-426d-90a0-e6fec4f51519

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_polynomial_sign

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
theorem _root_.solution : C7.PSignOfParts := fun _ _ _ => polynomial_sign
end Formalism.FourierDecayAlt.P
