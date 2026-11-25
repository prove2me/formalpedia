-- Prove2me | solution 1 for Formalism.L2.G.jW_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:27.905783+00:00
-- url     : https://prove2.me/submissions/782f6381-c908-469a-872b-e6a5e03f06f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution : jW p n (p : WQ p n) = (p : W2 p n) := map_natCast _ _
end Formalism.L2.G
