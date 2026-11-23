-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.X_mul_q_eq_one_add_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:27.372837+00:00
-- url     : https://prove2.me/submissions/b593c9de-4df1-4ae7-b2f7-ed79652c17ed

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_one_add_X_pow_alt

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
theorem _root_.solution : X * q l O = (1 + X) ^ l - 1 := by
  ext n
  rcases n with _ | m
  · simp [coeff_one_add_X_pow_alt]
  · simp [q, coeff_one_add_X_pow_alt, PowerSeries.coeff_succ_X_mul]
end Formalism.CohomologicalDescent.HeightDescentMinors
