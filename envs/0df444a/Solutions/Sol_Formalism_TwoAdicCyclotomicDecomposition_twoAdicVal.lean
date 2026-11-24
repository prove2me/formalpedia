-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.twoAdicVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:13.509561+00:00
-- url     : https://prove2.me/submissions/4d0a3295-4382-4bef-b703-0803ffc1707c

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_sq_split
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_val_even
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_TwoAdicValuation_val_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : TwoAdicVal := by
  intro a ha ha2 e he
  by_cases hev : Even e
  · have h := val_even a ha ha2 e he hev
    have hl : padicValNat 2 e ≤ Nat.log 2 e := padicValNat_le_nat_log e
    rw [if_pos hev]
    constructor <;> omega
  · have hod : Odd e := Nat.not_even_iff_odd.mp hev
    have h := val_odd a ha ha2 e hod
    have hs := sq_split a ha2
    rw [if_neg hev]
    constructor <;> omega
end Formalism.TwoAdicCyclotomicDecomposition
