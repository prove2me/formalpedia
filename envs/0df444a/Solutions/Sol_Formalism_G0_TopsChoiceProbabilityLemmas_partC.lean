-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.partC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.757189+00:00
-- url     : https://prove2.me/submissions/606180ae-0334-42ef-9b56-70d1e8b399df

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_marginal
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_le_card_eq_binUpper
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_binUpper_mono_trials
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_binUpper_mono_N
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_card_insert_inter
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_exists_le_sum
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
theorem _root_.solution (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (G' N₁ i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁) ≤
      n * binUpper G' δ (N₁ - 1) := by
  classical
  calc _ ≤ P ((range n).erase i₀) δ
        (fun t => ∃ i ∈ range n, N₁ ≤ (t ∩ (window n i G').erase i₀).card) := by
        apply P_mono h0 h1
        intro t _ h
        unfold CondIntervals at h
        push Not at h
        obtain ⟨i, hi, hN⟩ := h
        have hc := card_insert_inter i₀ t (window n i G')
        exact ⟨i, mem_range.2 hi, by omega⟩
    _ ≤ ∑ i ∈ range n, P ((range n).erase i₀) δ
        (fun t => N₁ ≤ (t ∩ (window n i G').erase i₀).card) :=
        prob_exists_le_sum h0 h1 (range n) (fun i t => N₁ ≤ (t ∩ (window n i G').erase i₀).card)
    _ = ∑ i ∈ range n, binUpper ((window n i G').erase i₀).card δ N₁ := by
        apply sum_congr rfl
        intro i _
        exact (prob_marginal δ (erase_subset_erase i₀ (window_subset n i G' hn))
          (fun a => N₁ ≤ a.card)).trans (prob_le_card_eq_binUpper _ δ N₁)
    _ ≤ ∑ i ∈ range n, binUpper G' δ (N₁ - 1) := by
        apply sum_le_sum
        intro i _
        exact (binUpper_mono_trials (card_erase_le.trans (window_card n i G')) h0 h1 N₁).trans
          (binUpper_mono_N G' h0 h1 N₁)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
end Formalism.G0.TopsChoiceProbabilityLemmas
