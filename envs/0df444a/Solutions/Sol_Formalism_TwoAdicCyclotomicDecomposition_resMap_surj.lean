-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.resMap_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:28.65056+00:00
-- url     : https://prove2.me/submissions/36a49357-16e1-4ab2-9843-5fda4284677e

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_resMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) : Function.Surjective (resMap h) := by
  rintro ⟨u, a, b⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (pow_dvd_pow 2 (by omega : s + 2 ≤ m + 2)) u
  exact ⟨(v, a, b), by rw [resMap_apply, hv]⟩
end Formalism.TwoAdicCyclotomicDecomposition
