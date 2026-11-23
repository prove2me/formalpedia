-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.mu_facts_hold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:14.872408+00:00
-- url     : https://prove2.me/submissions/bdeb954f-14fb-466a-88f6-48ef0222e5f8

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_existsUnique_teichmuller_lift
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_card_mu_eq_sub_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_roots_unity_eq_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : MuFacts := by
  intro l _
  exact ⟨card_mu_eq_sub_one l, existsUnique_teichmuller_lift l, prod_roots_unity_eq_neg_one l⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
