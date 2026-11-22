-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.mem_mu_iff_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:12.414718+00:00
-- url     : https://prove2.me/submissions/24d6951d-0977-459b-a3dd-1f56f50f5091

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
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {d : ℤ_[l]} : d ∈ mu l ↔ d ^ (l - 1) = 1 := by
  rw [mu, Polynomial.mem_nthRootsFinset (prime_sub_one_pos l)]
end Formalism.CohomologicalDescent.HeightDescentMinors
