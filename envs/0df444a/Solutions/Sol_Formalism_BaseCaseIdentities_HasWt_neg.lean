-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:35.776333+00:00
-- url     : https://prove2.me/submissions/2d5810f4-4283-4f05-935d-324c1b2ee39a

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd

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
theorem _root_.solution (hf : HasWt v r w f) : HasWt v r w (-f) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_neg, v.map_neg]
  exact hf A
end HasWt
end Formalism.BaseCaseIdentities
