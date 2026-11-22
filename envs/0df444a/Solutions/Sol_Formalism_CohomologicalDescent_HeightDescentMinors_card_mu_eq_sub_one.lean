-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.card_mu_eq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:25.725297+00:00
-- url     : https://prove2.me/submissions/e19fa9f6-c729-4f25-a7b0-a9668e04a8a7

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_mem_units_of_mem_mu
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_injOn_mu
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_surjOn_mu_nonzero

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
theorem _root_.solution : (mu l).card = l - 1 := by
  rw [Finset.card_nbij _ (toZMod_mem_units_of_mem_mu l) (toZMod_injOn_mu l) (toZMod_surjOn_mu_nonzero l),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
end Formalism.CohomologicalDescent.HeightDescentMinors
