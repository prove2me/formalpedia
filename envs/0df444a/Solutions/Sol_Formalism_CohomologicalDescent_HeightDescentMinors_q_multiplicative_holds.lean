-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.q_multiplicative_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:18.714925+00:00
-- url     : https://prove2.me/submissions/efac7d2e-f4b2-4ddb-8678-88446fd198a8

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_X_mul_q_eq_one_add_X_pow_sub_one

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
theorem _root_.solution : QMul := by
  intro l _ O _ _
  have hs : HasSubst ((1 + X) ^ l - 1 : O⟦X⟧) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    change PowerSeries.constantCoeff ((1 + X) ^ l - 1 : O⟦X⟧) = 0
    simp
  exact ⟨X_mul_q_eq_one_add_X_pow_sub_one l O, by rw [phi, PowerSeries.subst_X hs, X_mul_q_eq_one_add_X_pow_sub_one]⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
