-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.tiles_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:13.630557+00:00
-- url     : https://prove2.me/submissions/345f109c-4413-4d76-9c8c-a6681a79faf5

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_P_nonneg
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_forall_eq_prod
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_not_eq_one_sub
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_tile_disjoint
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_inter
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_tile_div
import Theorems.Thm_P2M_Formalism_G0_TopsChoiceProbabilityLemmas_tile_sub__fbbb87d340ca
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_insert
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_ge
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) (s₀ : ℕ) (hs₀ : s₀ < n / ((6 * r + 1) * u)) :
    P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
      ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) ≤
      (1 - markedBound δ r u) ^ M₀ := by
  classical
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hM : M₀ + 1 ≤ n / ((6 * r + 1) * u) := (Nat.le_div_iff_mul_le hℓpos).2 hn
  set tt := n / ((6 * r + 1) * u) with htt
  set J := (range (M₀ + 1)).image (fun j => (s₀ + j) % tt) with hJdef
  have hJ : J.card = M₀ + 1 := by
    rw [card_image_of_injOn, card_range]
    intro j hj j' hj' h
    simp only [coe_range, Set.mem_Iio] at hj hj'
    have := Nat.ModEq.add_left_cancel' s₀ h
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hF : M₀ ≤ (J.erase (i₀ / ((6 * r + 1) * u))).card := by
    have := pred_card_le_card_erase (s := J) (a := i₀ / ((6 * r + 1) * u))
    omega
  obtain ⟨F, hFs, hFc⟩ := exists_subset_card_eq hF
  have hFmem : ∀ s ∈ F, s ≠ i₀ / ((6 * r + 1) * u) ∧ s < tt ∧ ∃ j ≤ M₀, (s₀ + j) % tt = s := by
    intro s hs
    have := hFs hs
    rw [mem_erase, mem_image] at this
    obtain ⟨hs0, j, hj, hjs⟩ := this
    exact ⟨hs0, hjs ▸ Nat.mod_lt _ (by omega), j, by have := mem_range.1 hj; omega, hjs⟩
  have hnot : ∀ s ∈ F, i₀ ∉ tile r u s := fun s hs hmem => (hFmem s hs).1 (tile_div hmem).symm
  have hsub : ∀ s ∈ F, tile r u s ⊆ (range n).erase i₀ :=
    fun s hs => tile_sub' (hFmem s hs).2.1 (hnot s hs)
  calc _ ≤ P ((range n).erase i₀) δ (fun t => ∀ s ∈ F, ¬ Marked t r u s) := by
        apply P_mono h0 h1
        intro t _ h s hs
        obtain ⟨_, _, j, hj, hjs⟩ := hFmem s hs
        rw [← marked_insert t (hnot s hs), ← hjs]
        exact h j hj
    _ = ∏ s ∈ F, P ((range n).erase i₀) δ (fun t => ¬ Marked t r u s) :=
        prob_forall_eq_prod δ F (tile r u) hsub (fun s _ s' _ hne => tile_disjoint hne)
          (fun s t => ¬ Marked t r u s) (fun s _ t => not_congr (marked_inter t r u s))
    _ ≤ ∏ s ∈ F, (1 - markedBound δ r u) := by
        apply prod_le_prod
        · intro s _
          exact P_nonneg h0 h1 _
        · intro s hs
          rw [prob_not_eq_one_sub]
          linarith [marked_ge (r := r) (u := u) (s := s) h0 h1 (hsub s hs)]
    _ = _ := by rw [prod_const, hFc]
end Formalism.G0.TopsChoiceProbabilityLemmas
