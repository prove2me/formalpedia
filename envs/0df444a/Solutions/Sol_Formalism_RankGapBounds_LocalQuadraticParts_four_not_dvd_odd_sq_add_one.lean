-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.four_not_dvd_odd_sq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:53.60083+00:00
-- url     : https://prove2.me/submissions/60896084-5bdb-4744-be80-42b324ec431f

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
theorem _root_.solution (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := hy
  have h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2 := by ring
  rw [h]
  generalize k ^ 2 + k = t
  omega
end Formalism.RankGapBounds.LocalQuadraticParts
