-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.Final.rootUnityTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:08.216156+00:00
-- url     : https://prove2.me/submissions/0a1f9c2e-33b8-41f4-adee-768ae42897ee

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_eq_one_of_sub_one_mem_prime


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
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.RootUnityTriv := Formalism.SLP.GlobalBoundRefinements.P.eq_one_of_sub_one_mem_prime
end Formalism.SLP.GlobalBoundRefinements.Final
