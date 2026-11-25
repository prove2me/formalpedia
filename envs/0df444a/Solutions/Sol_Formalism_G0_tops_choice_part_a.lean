-- Prove2me | solution 1 for Formalism.G0.tops_choice_part_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:26.003857+00:00
-- url     : https://prove2.me/submissions/132149f8-9c86-48e7-af0c-e527134ce25d

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_condProb_eq
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_exists_le_sum
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_subset_eq_pow_card
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_subset
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_card
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_window_bound
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_key

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
open TopsConditionalProbabilityWindows
namespace Formalism.G0
theorem _root_.solution : TopsChoicePartA := by
  classical
  intro n δ L₂ K hn hδ hL hLδ
  have hL' : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  have hδ1 : δ ≤ 1 := by nlinarith
  have hn1 : 1 ≤ n := by omega
  rw [condProb_eq n hn1]
  set U := (range n).erase 0 with hU
  let F : ℕ → Finset (Finset ℕ) := fun i =>
    powersetCard (if 0 ∈ window n i L₂ then K else K + 1) ((window n i L₂).erase 0)
  calc P U δ (fun t => ¬ CondA n (insert 0 t) L₂ K)
      ≤ P U δ (fun t => ∃ i ∈ range n, ∃ S ∈ F i, S ⊆ t) := by
        apply P_mono hδ hδ1
        intro t ht h
        have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
        exact key n L₂ K t h0t h
    _ ≤ ∑ i ∈ range n, P U δ (fun t => ∃ S ∈ F i, S ⊆ t) :=
        prob_exists_le_sum hδ hδ1 (range n) (fun i t => ∃ S ∈ F i, S ⊆ t)
    _ ≤ ∑ i ∈ range n, ∑ S ∈ F i, P U δ (fun t => S ⊆ t) :=
        sum_le_sum fun i _ => prob_exists_le_sum hδ hδ1 (F i) (fun S t => S ⊆ t)
    _ = ∑ i ∈ range n, ∑ S ∈ F i, δ ^ S.card := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro S hS
        apply prob_subset_eq_pow_card
        intro x hx
        have hx' := (mem_powersetCard.1 hS).1 hx
        exact mem_erase.2 ⟨(mem_erase.1 hx').1, window_subset n i L₂ hn1 (mem_erase.1 hx').2⟩
    _ ≤ ∑ i ∈ range n, (L₂.choose K : ℝ) * δ ^ K :=
        sum_le_sum fun i _ => window_bound δ hδ L₂ K hLδ _ (window_card n i L₂)
    _ = n * (L₂.choose K : ℝ) * δ ^ K := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring
end Formalism.G0
