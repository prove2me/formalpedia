-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.partA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:35.04509+00:00
-- url     : https://prove2.me/submissions/54231cdf-8204-4bd8-bc83-66087184947c

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_card_insert_inter
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_exists_le_sum
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_subset_eq_pow_card
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_card
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_subset


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
theorem _root_.solution (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (L₂ K i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) ≤
      n * (L₂.choose K : ℝ) * δ ^ K := by
  classical
  let F : ℕ → Finset (Finset ℕ) := fun i => powersetCard K ((window n i L₂).erase i₀)
  calc _ ≤ P ((range n).erase i₀) δ (fun t => ∃ i ∈ range n, ∃ S ∈ F i, S ⊆ t) := by
        apply P_mono h0 h1
        intro t _ h
        unfold CondA at h
        push Not at h
        obtain ⟨i, hi, hK⟩ := h
        have hc := card_insert_inter i₀ t (window n i L₂)
        obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq
          (show K ≤ (t ∩ (window n i L₂).erase i₀).card by omega)
        exact ⟨i, mem_range.2 hi, S, mem_powersetCard.2 ⟨hS.trans inter_subset_right, hSc⟩,
          hS.trans inter_subset_left⟩
    _ ≤ ∑ i ∈ range n, P ((range n).erase i₀) δ (fun t => ∃ S ∈ F i, S ⊆ t) :=
        prob_exists_le_sum h0 h1 (range n) (fun i t => ∃ S ∈ F i, S ⊆ t)
    _ ≤ ∑ i ∈ range n, ∑ S ∈ F i, P ((range n).erase i₀) δ (fun t => S ⊆ t) :=
        sum_le_sum fun i _ => prob_exists_le_sum h0 h1 (F i) (fun S t => S ⊆ t)
    _ = ∑ i ∈ range n, ∑ S ∈ F i, δ ^ S.card := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro S hS
        apply prob_subset_eq_pow_card
        exact (mem_powersetCard.1 hS).1.trans (erase_subset_erase i₀ (window_subset n i L₂ hn))
    _ = ∑ i ∈ range n, (((window n i L₂).erase i₀).card.choose K : ℝ) * δ ^ K := by
        apply sum_congr rfl
        intro i _
        rw [sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]), sum_const,
          card_powersetCard, nsmul_eq_mul]
    _ ≤ ∑ i ∈ range n, (L₂.choose K : ℝ) * δ ^ K := by
        apply sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
        exact_mod_cast Nat.choose_le_choose K (card_erase_le.trans (window_card n i L₂))
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
end Formalism.G0.TopsChoiceProbabilityLemmas
