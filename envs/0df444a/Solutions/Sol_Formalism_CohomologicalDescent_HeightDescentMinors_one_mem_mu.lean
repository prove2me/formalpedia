-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.one_mem_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:41.471058+00:00
-- url     : https://prove2.me/submissions/3f976bc7-cda7-47cd-bc48-ee86b49cc264

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : (1 : ℤ_[l]) ∈ mu l := by
  rw [mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l), one_pow]
end Formalism.CohomologicalDescent.HeightDescentMinors
