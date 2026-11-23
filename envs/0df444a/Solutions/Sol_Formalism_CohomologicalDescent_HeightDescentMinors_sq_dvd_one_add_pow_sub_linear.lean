-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.sq_dvd_one_add_pow_sub_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:11.291801+00:00
-- url     : https://prove2.me/submissions/09950087-d7d5-4e74-ad23-2fa7e0fd5e9f

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_one_add_pow_eq_linear_add_sq_mul

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (R : Type) [CommRing R] (x v : R) (n : ℕ) :
    x ^ 2 ∣ (1 + x * v) ^ n - (1 + (n : R) * (x * v)) := by
  obtain ⟨e, he⟩ := one_add_pow_eq_linear_add_sq_mul (x * v) n
  rw [he]
  exact ⟨v ^ 2 * e, by ring⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
