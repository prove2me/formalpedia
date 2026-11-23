-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.zmod_int_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:28.103768+00:00
-- url     : https://prove2.me/submissions/10844dd7-dfee-4438-86cb-1aa80efb665d

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]
end Formalism.RankGapBounds.LocalQuadraticParts
