-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:32.07274+00:00
-- url     : https://prove2.me/submissions/d44a9567-6471-4b41-9b84-1d6a19309a5e

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
theorem _root_.solution (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f + g) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_add]
  exact le_trans (le_min (hf A) (hg A)) (v.map_add _ _)
end HasWt
end Formalism.BaseCaseIdentities
