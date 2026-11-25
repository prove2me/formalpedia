-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.binomRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:30.404318+00:00
-- url     : https://prove2.me/submissions/b253ae03-96a1-4a2b-9a76-499fb31d0418

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_ratio_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.BinomRatio := Formalism.CountingSumsFrames.binomial_ratio_bound
end Formalism.CountingSumsFrames.Top
