-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityWindows.window_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:43:29.719891+00:00
-- url     : https://prove2.me/submissions/fe575786-fc35-4452-87c1-fffb0aa2a6d8

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA

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
open Formalism.G0.TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsConditionalProbabilityWindows
theorem _root_.solution (δ : ℝ) (h0 : 0 ≤ δ) (L K : ℕ) (hLδ : (L : ℝ) * δ ≤ 1) (W : Finset ℕ)
    (hW : W.card ≤ L) :
    ∑ S ∈ powersetCard (if 0 ∈ W then K else K + 1) (W.erase 0), δ ^ S.card
      ≤ (L.choose K : ℝ) * δ ^ K := by
  classical
  have hs : ∀ m : ℕ, ∑ S ∈ powersetCard m (W.erase 0), δ ^ S.card
      = ((W.erase 0).card.choose m : ℝ) * δ ^ m := by
    intro m
    rw [sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]), sum_const,
      card_powersetCard, nsmul_eq_mul]
  have hE : (W.erase 0).card ≤ L := card_erase_le.trans hW
  have hδK : 0 ≤ δ ^ K := by positivity
  by_cases hw : 0 ∈ W
  · rw [if_pos hw, hs]
    have : (((W.erase 0).card.choose K : ℕ) : ℝ) ≤ (L.choose K : ℝ) := by
      exact_mod_cast Nat.choose_le_choose K hE
    exact mul_le_mul_of_nonneg_right this hδK
  · rw [if_neg hw, hs]
    have h1 : (((W.erase 0).card.choose (K + 1) : ℕ) : ℝ) ≤ (L.choose (K + 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose (K + 1) hE
    have h2 : (L.choose (K + 1) : ℝ) * δ ^ (K + 1) ≤ (L.choose K : ℝ) * δ ^ K := by
      have e : (L.choose (K + 1) : ℝ) * ((K : ℝ) + 1) = (L.choose K : ℝ) * ((L - K : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq L K
      have hle : ((L - K : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L K
      have hC : 0 ≤ (L.choose K : ℝ) := Nat.cast_nonneg _
      have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      have key : (L.choose (K + 1) : ℝ) * δ ^ (K + 1) * ((K : ℝ) + 1)
          ≤ (L.choose K : ℝ) * δ ^ K * ((K : ℝ) + 1) := by
        calc (L.choose (K + 1) : ℝ) * δ ^ (K + 1) * ((K : ℝ) + 1)
            = ((L.choose (K + 1) : ℝ) * ((K : ℝ) + 1)) * δ * δ ^ K := by ring
          _ = (L.choose K : ℝ) * ((L - K : ℕ) : ℝ) * δ * δ ^ K := by rw [e]
          _ ≤ (L.choose K : ℝ) * (L : ℝ) * δ * δ ^ K := by gcongr
          _ = (L.choose K : ℝ) * δ ^ K * ((L : ℝ) * δ) := by ring
          _ ≤ (L.choose K : ℝ) * δ ^ K * 1 :=
              mul_le_mul_of_nonneg_left hLδ (mul_nonneg hC hδK)
          _ ≤ (L.choose K : ℝ) * δ ^ K * ((K : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hδK)
      exact le_of_mul_le_mul_right key (by linarith)
    calc (((W.erase 0).card.choose (K + 1) : ℕ) : ℝ) * δ ^ (K + 1)
        ≤ (L.choose (K + 1) : ℝ) * δ ^ (K + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := h2
end Formalism.G0.TopsConditionalProbabilityWindows
