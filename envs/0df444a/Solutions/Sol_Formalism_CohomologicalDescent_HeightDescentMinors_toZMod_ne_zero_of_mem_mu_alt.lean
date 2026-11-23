-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:12.09024+00:00
-- url     : https://prove2.me/submissions/11da1305-4f1d-4ee2-b64e-e57f4eb8d8e8

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
theorem _root_.solution {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := toZMod_ne_zero_of_mem_mu l hd
end Formalism.CohomologicalDescent.HeightDescentMinors
