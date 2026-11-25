-- Prove2me | solution 1 for Formalism.BasicNotions.Host.five_le_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:06.940814+00:00
-- url     : https://prove2.me/submissions/b7601fb5-96e2-47ad-b9a4-027ddc8e85a8

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
import Theorems.Thm_Formalism_BasicNotions_Host_splitBound_lt_of_inert

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
theorem _root_.solution (hp : p.Prime) (h3 : 3 ≤ H.splitBound) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : 5 ≤ p := by
  have h1 := H.splitBound_lt_of_inert hp h
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
  omega
end Formalism.BasicNotions.Host
