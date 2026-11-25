-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.v_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:54.130488+00:00
-- url     : https://prove2.me/submissions/0cde8be9-c0c8-40b6-b979-b09cdd5e5c60

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution (v : AddValuation k (WithTop ℝ)) (n : ℕ) : 0 ≤ v (n : k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    refine le_trans (le_min ih ?_) (v.map_add _ _)
    rw [v.map_one]
end Formalism.BaseCaseIdentities
