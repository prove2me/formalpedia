-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:47.396118+00:00
-- url     : https://prove2.me/submissions/2ae8ba7d-a59e-45c1-af59-92ff62cc3060

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_neg

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
theorem _root_.solution (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
end HasWt
end Formalism.BaseCaseIdentities
