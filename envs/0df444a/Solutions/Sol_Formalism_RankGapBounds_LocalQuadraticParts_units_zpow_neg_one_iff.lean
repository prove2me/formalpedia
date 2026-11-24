-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.units_zpow_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:04.202943+00:00
-- url     : https://prove2.me/submissions/8afc681b-4d76-45ba-9cc4-f5f57656d7a9

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
theorem _root_.solution (n : ℕ) (u : (ZMod n)ˣ) :
    (∃ k : ℤ, (-1 : (ZMod n)ˣ) ^ k = u) ↔ (u = 1 ∨ u = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩
end Formalism.RankGapBounds.LocalQuadraticParts
