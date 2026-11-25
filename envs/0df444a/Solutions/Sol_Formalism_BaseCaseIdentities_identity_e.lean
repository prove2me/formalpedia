-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.identity_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:34.176844+00:00
-- url     : https://prove2.me/submissions/9a72a325-3024-4e3f-9226-072709e990cc

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Theorems.Thm_Formalism_BaseCaseIdentities_eNum_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BaseCaseIdentities
namespace Formalism.BaseCaseIdentities
theorem _root_.solution : IdE := by
  intro l s hl
  have hq : 2 ≤ l ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eNum_eq_sum hl]; simp
  · rw [eNum_eq_sum hl, eNum_eq_sum hl, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ, pow_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [eNum_eq_sum hl]
    have := geom_sum_mul_add (l ^ 2 - 1) s
    rwa [Nat.sub_add_cancel (by omega)] at this
end Formalism.BaseCaseIdentities
