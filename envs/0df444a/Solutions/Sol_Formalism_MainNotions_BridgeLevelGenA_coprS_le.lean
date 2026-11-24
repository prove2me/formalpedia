-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenA.coprS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:58.818828+00:00
-- url     : https://prove2.me/submissions/703f894a-7c1a-40ed-bc03-a36b12df9ed6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
namespace Formalism.MainNotions.BridgeLevelGenA
theorem _root_.solution (g : R) : coprS g ≤ R⁰ := fun _ hs => mem_nonZeroDivisors_of_ne_zero hs.2
end Formalism.MainNotions.BridgeLevelGenA
