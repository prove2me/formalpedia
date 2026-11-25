-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.eNum_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:29.187415+00:00
-- url     : https://prove2.me/submissions/55cfee9b-e849-4e71-8a95-7f7b474e1891

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB

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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (s : ℕ) :
    eNum l s = ∑ j ∈ Finset.range s, (l ^ 2) ^ j := by
  have : 2 ≤ l ^ 2 := by nlinarith
  unfold eNum; rw [Nat.geomSum_eq this]
end Formalism.BaseCaseIdentities
