-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_mem_units_of_mem_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:15.459505+00:00
-- url     : https://prove2.me/submissions/7b7a9163-50a4-4786-9b29-1e80df1ce3ad

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_ne_zero_of_mem_mu

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
theorem _root_.solution : ∀ d ∈ mu l, PadicInt.toZMod d ∈ (univ.erase (0 : ZMod l)) := fun d hd => Finset.mem_erase.mpr ⟨toZMod_ne_zero_of_mem_mu l hd, Finset.mem_univ _⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
