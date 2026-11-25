-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.Final.rootUnityModT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:01.351667+00:00
-- url     : https://prove2.me/submissions/ec92cd12-460b-4bf9-99ff-9a30a253e6b3

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_root_of_unity_mod_t


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
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.RootUnityModT := Formalism.SLP.GlobalBoundRefinements.P.root_of_unity_mod_t
end Formalism.SLP.GlobalBoundRefinements.Final
