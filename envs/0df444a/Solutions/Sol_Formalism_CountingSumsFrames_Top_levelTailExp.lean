-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.levelTailExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:37.868485+00:00
-- url     : https://prove2.me/submissions/daa936e0-c2a4-48e7-8282-8f1851cd26e0

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Definitions.Def_Formalism_PolynomialDimension_DigitClassCount
import Theorems.Thm_Formalism_CountingSumsFrames_level_tail_exp_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.LevelTailExp := Formalism.CountingSumsFrames.level_tail_exp_bound
end Formalism.CountingSumsFrames.Top
