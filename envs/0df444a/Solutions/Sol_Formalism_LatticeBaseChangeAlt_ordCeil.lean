-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.ordCeil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:32.837825+00:00
-- url     : https://prove2.me/submissions/9191bfc6-5636-4972-888f-5c0ce29317a8

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : OrdCeil := by
  intro n x h
  have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have h2 : (-(⌈x⌉ : ℝ) - 1) < (n : ℝ) := by linarith
  have h3 : (-⌈x⌉ - 1 : ℤ) < n := by exact_mod_cast h2
  omega
end Formalism.LatticeBaseChangeAlt
