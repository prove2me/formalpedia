-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.identity_twenty_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:34.916302+00:00
-- url     : https://prove2.me/submissions/f51d2696-b0a3-4a78-987a-b3934b7cb413

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
theorem _root_.solution : PowMulThreeEighthsIdentity := by
  intro l i hl hi
  obtain ⟨t, rfl⟩ := hi
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l:ℝ) ≠ 0 := by linarith
  have hs : Kn (2 * t + 1) = t + 1 := by unfold Kn; omega
  rw [hs]
  unfold qnum sg; field_simp; ring
end Formalism.BaseCaseIdentities
