-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.theoremM_of_tieOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:20:56.119972+00:00
-- url     : https://prove2.me/submissions/ba45edf9-fc9e-4f2f-80f5-1dba24e70731

import Definitions.Def_Formalism_MahlerMeasure_FinalT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Theorems.Thm_Formalism_CountingSumsFrames_Top_partnerM_of_tieOps
import Theorems.Thm_Formalism_CountingSumsFrames_monomial_count
import Theorems.Thm_Formalism_CountingSumsFrames_partnerM_of_tieOps
import Theorems.Thm_Formalism_GM_Top_badCrit
import Theorems.Thm_Formalism_GM_Top_meanGam
import Theorems.Thm_Formalism_GM_smith_form_p_adic_integers
import Theorems.Thm_Formalism_GM_theoremM_of_partner
import Theorems.Thm_Formalism_GM_weight_space_dimension_monotone


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
theorem _root_.solution (h : Formalism.CountingSumsFrames.TieOps) : M.TheoremM :=
  theoremM_of_partner Formalism.GM.Top.meanGam Formalism.GM.weight_space_dimension_monotone Formalism.CountingSumsFrames.monomial_count Formalism.GM.Top.badCrit
    Formalism.GM.smith_form_p_adic_integers (Formalism.CountingSumsFrames.partnerM_of_tieOps h)
end Formalism.CountingSumsFrames.Top
