-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.zmod_nat_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:25.507446+00:00
-- url     : https://prove2.me/submissions/f41ee56e-2957-43fd-bdb6-c3363d4f67cf

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_int_eq_one_iff

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
theorem _root_.solution (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by
  have h := zmod_int_eq_one_iff n (l : ℤ)
  simpa using h
end Formalism.RankGapBounds.LocalQuadraticParts
