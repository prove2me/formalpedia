-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.two_le_mul_abs_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:07.15137+00:00
-- url     : https://prove2.me/submissions/0cb282aa-80c8-4765-9ce1-e99945e440b3

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealLargeTOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg t]
end Formalism.ZeroFreeDirichlet
