-- Prove2me | solution 1 for Formalism.L2.LamCM.exists_finset_card_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:47.157731+00:00
-- url     : https://prove2.me/submissions/017460e3-e162-413f-9e9a-0e35070e8d62

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {k : Type} (D : ℕ) (h : Infinite k ∨ D < Nat.card k) : ∃ S : Finset k, D < S.card := by
  rcases h with h | h
  · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq k (D + 1)
    exact ⟨S, by omega⟩
  · have : Finite k := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite k
    refine ⟨Finset.univ, ?_⟩
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
end Formalism.L2.LamCM
