-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.partnerM_of_tieOps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:11.754693+00:00
-- url     : https://prove2.me/submissions/596e125e-9f9a-41ba-97c2-6acd08d0e60d

import Definitions.Def_Formalism_MahlerMeasure_FinalT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Theorems.Thm_Formalism_CountingSumsFrames_partnerM_of_tieOps


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
theorem _root_.solution (h : Formalism.CountingSumsFrames.TieOps) : TM.PartnerM := Formalism.CountingSumsFrames.partnerM_of_tieOps h
end Formalism.CountingSumsFrames.Top
