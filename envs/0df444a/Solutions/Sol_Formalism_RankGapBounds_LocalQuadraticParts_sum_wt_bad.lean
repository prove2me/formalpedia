-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:01.932348+00:00
-- url     : https://prove2.me/submissions/6ae4ef92-4d60-4f0c-898f-a510b02cc920

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
theorem _root_.solution {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)] (hω : ∀ p, 0 ≤ ω p)
    (hBAD : ∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
      wt δ T ≤ β * δ) :
    ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α * ∑ p, ω p := by
  have key : ∀ p, ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) ≤
      β * δ * Fintype.card α := by
    intro p
    have e : ∀ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) =
        ∑ t : α, if t ∈ T ∧ BAD p t T then wt δ T else 0 := by
      intro T
      have hf : (Finset.univ : Finset α).filter (fun t => t ∈ T ∧ BAD p t T) =
          T.filter fun t => BAD p t T := by
        ext t; simp
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, mul_comm]
    calc ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ)
        = ∑ T : Finset α, ∑ t : α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) :=
          Finset.sum_congr rfl (fun T _ => e T)
      _ = ∑ t : α, ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then wt δ T else 0) := Finset.sum_comm
      _ = ∑ t : α, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
            wt δ T := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ _t : α, β * δ := Finset.sum_le_sum (fun t _ => hBAD p t)
      _ = β * δ * Fintype.card α := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc ∑ T : Finset α, wt δ T * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ)
      = ∑ p, ω p * ∑ T : Finset α, wt δ T * ((T.filter fun t => BAD p t T).card : ℝ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun T _ => ?_))
        ring
    _ ≤ ∑ p, ω p * (β * δ * Fintype.card α) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (key p) (hω p))
    _ = β * δ * Fintype.card α * ∑ p, ω p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
end Formalism.RankGapBounds.LocalQuadraticParts
