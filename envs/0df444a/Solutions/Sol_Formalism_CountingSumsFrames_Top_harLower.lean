-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.harLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:36:31.877193+00:00
-- url     : https://prove2.me/submissions/ecff8dce-7b63-402b-93c1-1986b1b5ab5f

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Theorems.Thm_Formalism_CountingSumsFrames_harmonic_lower_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.HarLower := Formalism.CountingSumsFrames.harmonic_lower_bound
end Formalism.CountingSumsFrames.Top
