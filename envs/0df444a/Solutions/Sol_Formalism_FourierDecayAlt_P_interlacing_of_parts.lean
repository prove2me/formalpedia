-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.interlacing_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:02.717447+00:00
-- url     : https://prove2.me/submissions/91d14e4b-4a05-4427-9abb-581cda08599c

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing

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
theorem _root_.solution : C7.LemmaEInterlacingOfParts := by
  unfold C7.LemmaEInterlacingOfParts C7.LemmaEInterlacing LE.LemmaE
  intro hE hR CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S u u' l hl hlk hI hI' hB hN hL hβ
  exact hE CR Cd CP h1 h2 h3 C₂ hC₂ C₆ hC₆ S hN hL hβ (hR S u u' l hl hlk hI hI' hB)
end Formalism.FourierDecayAlt.P
