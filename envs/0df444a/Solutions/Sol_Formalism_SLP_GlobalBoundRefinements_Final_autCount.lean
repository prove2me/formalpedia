-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.Final.autCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:40.317531+00:00
-- url     : https://prove2.me/submissions/d377301d-a7c6-4bd5-b58f-41c743eb2d8c

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_card_linearEquiv_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.Final
namespace Formalism.SLP.GlobalBoundRefinements.Final
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.AutCount := Formalism.SLP.GlobalBoundRefinements.P.card_linearEquiv_le
end Formalism.SLP.GlobalBoundRefinements.Final
