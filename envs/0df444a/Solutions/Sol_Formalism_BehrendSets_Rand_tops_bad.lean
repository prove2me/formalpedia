-- Prove2me | solution 1 for Formalism.BehrendSets.Rand.tops_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:27.070703+00:00
-- url     : https://prove2.me/submissions/609c26ef-bb66-4fb0-a35d-c904dc490c68

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_sub_le
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_mono
import Theorems.Thm_Formalism_BehrendSets_Rand_prob_exists_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.Rand
theorem _root_.solution (X : Finset α) (δ : ℝ) (L K : ℕ) (t : α) (𝒲 : Finset (Finset α))
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hW : ∀ W ∈ 𝒲, W.card ≤ L) :
    prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
      ≤ δ * 𝒲.card * ((L : ℝ) * δ) ^ K := by
  calc prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
      ≤ prob X δ (fun T => ∃ W ∈ 𝒲, ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T) := by
        apply prob_mono X h0 h1
        rintro T - ⟨htT, W, hW𝒲, hK⟩
        refine ⟨W, hW𝒲, ?_⟩
        have hA : K ≤ ((T ∩ W).erase t).card := by
          have := pred_card_le_card_erase (s := T ∩ W) (a := t)
          omega
        obtain ⟨S, hSA, hSc⟩ := exists_subset_card_eq hA
        refine ⟨S, mem_powersetCard.mpr ⟨hSA.trans (erase_subset_erase t inter_subset_right), hSc⟩,
          ?_⟩
        exact insert_subset htT (hSA.trans ((erase_subset t _).trans inter_subset_left))
    _ ≤ ∑ W ∈ 𝒲, prob X δ (fun T => ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T) :=
        prob_exists_le X h0 h1 𝒲
          (fun W T => ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T)
    _ ≤ ∑ W ∈ 𝒲, ∑ S ∈ powersetCard K (W.erase t), prob X δ (fun T => insert t S ⊆ T) :=
        Finset.sum_le_sum fun W _ => prob_exists_le X h0 h1 _ (fun S T => insert t S ⊆ T)
    _ ≤ ∑ W ∈ 𝒲, ∑ S ∈ powersetCard K (W.erase t), δ ^ (K + 1) := by
        apply Finset.sum_le_sum
        intro W _
        apply Finset.sum_le_sum
        intro S hS
        have hS' := mem_powersetCard.mp hS
        have htS : t ∉ S := fun h => (mem_erase.mp (hS'.1 h)).1 rfl
        have hc : (insert t S).card = K + 1 := by rw [card_insert_of_notMem htS, hS'.2]
        rw [← hc]
        exact prob_sub_le X _ h0
    _ ≤ ∑ W ∈ 𝒲, (L : ℝ) ^ K * δ ^ (K + 1) := by
        apply Finset.sum_le_sum
        intro W hW𝒲
        rw [Finset.sum_const, card_powersetCard, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
        have h2 : (W.erase t).card.choose K ≤ L ^ K :=
          (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (card_erase_le.trans (hW W hW𝒲)) K)
        exact_mod_cast h2
    _ = δ * 𝒲.card * ((L : ℝ) * δ) ^ K := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
        ring
end Formalism.BehrendSets.Rand
