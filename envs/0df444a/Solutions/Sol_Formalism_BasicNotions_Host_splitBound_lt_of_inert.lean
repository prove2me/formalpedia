-- Prove2me | solution 1 for Formalism.BasicNotions.Host.splitBound_lt_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:48:49.08307+00:00
-- url     : https://prove2.me/submissions/ea20ac1a-28b5-4ddf-a4c6-4ce07a596ffa

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
import Theorems.Thm_Formalism_BasicNotions_Host_not_inert_of_le_splitBound

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
theorem _root_.solution (hp : p.Prime) (h : H.cls p = .signal ∨ H.cls p = .inertClass) : H.splitBound < p :=
  lt_of_not_ge fun hle => H.not_inert_of_le_splitBound hp hle h
end Formalism.BasicNotions.Host
