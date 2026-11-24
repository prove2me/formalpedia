-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.tops_lemma_six_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:03.096791+00:00
-- url     : https://prove2.me/submissions/f7da6c31-f6c0-4ed4-9f06-267d3de144df

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_wt_nonneg
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sum_wt
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sum_wt_var
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_sum_wt_bad
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pick

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
theorem _root_.solution : TopsFixed := by
  intro α ι _ _ _ δ β ω BAD _ hδ0 hδ1 hq hβ hω hBAD
  have hS : 0 ≤ ∑ p, ω p := Finset.sum_nonneg fun p _ => hω p
  have hN : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hqpos : 0 < δ * Fintype.card α := by linarith
  obtain ⟨T, -, hVT, hXT⟩ := pick (Finset.univ : Finset (Finset α)) (wt δ)
    (fun T => ((T.card : ℝ) - δ * Fintype.card α) ^ 2)
    (fun T => ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ))
    ((δ * Fintype.card α / 2) ^ 2) (β * δ * Fintype.card α * ∑ p, ω p)
    (by positivity) (by positivity)
    (fun T _ => wt_nonneg hδ0.le hδ1 T) (sum_wt δ) (fun T _ => sq_nonneg _)
    (by
      rw [sum_wt_var δ]
      nlinarith [mul_nonneg hqpos.le hδ0.le,
        mul_nonneg hqpos.le (by linarith : (0 : ℝ) ≤ δ * Fintype.card α - 6)])
    (fun T _ => Finset.sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _))
    (sum_wt_bad δ β ω BAD hω hBAD)
  have hab := abs_lt_of_sq_lt_sq' hVT (by positivity)
  refine ⟨T, by linarith [hab.1], by linarith [hab.2], by linarith⟩
end Formalism.RankGapBounds.LocalQuadraticParts
