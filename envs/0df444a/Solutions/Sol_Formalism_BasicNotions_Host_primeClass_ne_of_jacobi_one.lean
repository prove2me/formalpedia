-- Prove2me | solution 1 for Formalism.BasicNotions.Host.primeClass_ne_of_jacobi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:10:30.297781+00:00
-- url     : https://prove2.me/submissions/9a65ae7c-d457-4044-83e5-0ce1552f579c

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_inert_iff


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
theorem _root_.solution (h : jacobiSym (-(H.d : ℤ)) p = 1) : H.cls p ≠ .inertClass := fun e =>
  ((primeClass_eq_inert_iff H.toHostRaw).1 e).2.2.2.1 h
end Formalism.BasicNotions.Host
