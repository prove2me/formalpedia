-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.hockeyStick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:32.639103+00:00
-- url     : https://prove2.me/submissions/68e11ecd-b447-4a57-9a56-64abf57d7ca1

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Theorems.Thm_Formalism_CountingSumsFrames_hockey_stick_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.HockeyStick := Formalism.CountingSumsFrames.hockey_stick_identity
end Formalism.CountingSumsFrames.Top
