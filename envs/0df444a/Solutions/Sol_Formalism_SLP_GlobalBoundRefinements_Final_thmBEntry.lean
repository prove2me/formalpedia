-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.Final.thmBEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:24:18.474803+00:00
-- url     : https://prove2.me/submissions/9dea1670-7467-4fc9-8d22-1f1a73c0855d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_theorem_B_entry_formula


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
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.ThmBEntry := Formalism.SLP.GlobalBoundRefinements.P.theorem_B_entry_formula
end Formalism.SLP.GlobalBoundRefinements.Final
