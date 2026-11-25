-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:40:51.705815+00:00
-- url     : https://prove2.me/submissions/07b30336-aaf8-4a4d-87e8-8f45e70e6ec3

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_one

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
namespace HasWt
theorem _root_.solution (hf : HasWt v r w f) (n : ℕ) : HasWt v r ((n : ℝ) * w) (f ^ n) := by
  induction n with
  | zero => simpa using (HasWt.one : HasWt v r 0 (1 : MvPowerSeries Z k))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring
end HasWt
end Formalism.BaseCaseIdentities
