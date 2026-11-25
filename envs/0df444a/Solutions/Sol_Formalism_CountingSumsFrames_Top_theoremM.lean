-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.theoremM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:18.5153+00:00
-- url     : https://prove2.me/submissions/a2adbe25-c43e-432f-9907-8875cc962c08

import Definitions.Def_Formalism_MahlerMeasure_FinalT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Theorems.Thm_Formalism_CountingSumsFrames_Top_theoremM_of_tieOps
import Theorems.Thm_Formalism_CountingSumsFrames_level_operators_exist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
open Formalism.GM
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : M.TheoremM := theoremM_of_tieOps Formalism.CountingSumsFrames.level_operators_exist
end Formalism.CountingSumsFrames.Top
