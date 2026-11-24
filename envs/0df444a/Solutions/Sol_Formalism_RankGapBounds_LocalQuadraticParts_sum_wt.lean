-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.sum_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:00.932809+00:00
-- url     : https://prove2.me/submissions/1712a662-4224-4eee-b6f9-c8ac3d265b73

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution {α : Type*} [Fintype α] (δ : ℝ) : ∑ T : Finset α, wt δ T = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow δ (1 - δ) (Finset.univ : Finset α)
  rw [Finset.powerset_univ, Finset.card_univ] at h
  simp only [wt]
  rw [h]
  simp
end Formalism.RankGapBounds.LocalQuadraticParts
