-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.Final.sEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:14.461136+00:00
-- url     : https://prove2.me/submissions/51b9b46f-aa6e-4be0-a978-69fec9119459

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_s_matrix_entry_formula


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
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.SEntry := Formalism.SLP.GlobalBoundRefinements.P.s_matrix_entry_formula
end Formalism.SLP.GlobalBoundRefinements.Final
