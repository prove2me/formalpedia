-- Prove2me | solution 1 for Formalism.BasicNotions.Host.cls_splitK_or_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:22:13.218083+00:00
-- url     : https://prove2.me/submissions/3c86239e-26d0-4c37-a720-94d4b044bfd5

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_splitK_iff
import Theorems.Thm_Formalism_HC_HostRaw_two_mem_small


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R) {p : ℕ}
namespace Formalism.BasicNotions.Host
theorem _root_.solution (hp : p.Prime) (h : p ≤ H.splitBound) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    H.cls p = .splitK ∨ p ∈ H.small := by
  by_cases hs : p ∈ H.small
  · exact Or.inr hs
  · have h2 : p ≠ 2 := fun e => hs (e ▸ H.two_mem_small)
    exact Or.inl ((primeClass_eq_splitK_iff H.toHostRaw).2 ⟨hs, hq, hd, H.split_small p hp h2 h⟩)
end Formalism.BasicNotions.Host
