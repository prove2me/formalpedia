-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.binomTail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:39.447314+00:00
-- url     : https://prove2.me/submissions/c5f41d89-da73-4ff5-812d-568b5c94c783

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_tail_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.BinomTail := Formalism.CountingSumsFrames.binomial_tail_bound
end Formalism.CountingSumsFrames.Top
