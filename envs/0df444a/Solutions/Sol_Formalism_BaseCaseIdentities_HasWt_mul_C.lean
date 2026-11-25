-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:52.634364+00:00
-- url     : https://prove2.me/submissions/be30b3b0-dbc9-4f42-8896-0546dae39315

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul

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
theorem _root_.solution {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (f * C x) := by
  rw [mul_comm]; exact hf.C_mul hx
end HasWt
end Formalism.BaseCaseIdentities
