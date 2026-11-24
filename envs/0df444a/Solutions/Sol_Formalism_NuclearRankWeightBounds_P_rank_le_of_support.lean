-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.rank_le_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:24.901989+00:00
-- url     : https://prove2.me/submissions/146c0b84-3956-41c1-b6e1-9c92278c20e7

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (S S' : Finset (Fin N))
    (h : ∀ a b, A a b ≠ 0 → a ∈ S ∧ b ∈ S') : A.rank ≤ min S.card S'.card := by
  refine le_min ?_ ?_
  · apply Matrix.rank_le_card_of_support_subset A S
    intro a ha
    by_contra hn
    apply ha
    funext b
    by_contra hb
    exact hn (h a b hb).1
  · rw [← Matrix.rank_transpose]
    apply Matrix.rank_le_card_of_support_subset Aᵀ S'
    intro b hb'
    by_contra hn
    apply hb'
    funext a
    by_contra ha
    exact hn (h a b ha).2
end Formalism.NuclearRankWeightBounds.P
