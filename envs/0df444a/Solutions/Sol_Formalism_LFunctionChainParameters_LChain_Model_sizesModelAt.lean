-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.Model.sizesModelAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:05.36214+00:00
-- url     : https://prove2.me/submissions/c849a636-ae94-4b83-915d-26edbeb2ab24

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_le_rpow_26
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_hostFacts_DA
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fPl_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_wM_cases
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_log_wM
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fM_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_identM

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.Model
theorem _root_.solution (cardHM : Fintype.card H = 65536) : SizesModelAt H := by
  have hx : (1 : ℝ) ≤ 65536 := by norm_num
  have hnT : (modelData (H := H)).nT = 65536 := by
    unfold Data.nT
    rw [Fintype.card_coe, Finset.card_univ, cardHM]
    norm_num
  have hcu : (univ : Finset H).card = 65536 := by rw [Finset.card_univ, cardHM]
  refine ⟨(univ : Finset H), inferInstance, 1, fM H, modelData, CM, 0, 1, 1,
    DA, fun _ => 0, 1048576, univ, univ, aM, wM, Equiv.refl _, ePM, 0, 2 ^ 20, 1 / 2 ^ 60,
    hostFacts_DA, identM, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_,
    by positivity, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  ·
    refine ⟨hx, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by rw [hnT]; norm_num, ?_,
      by norm_num [modelData], by norm_num, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData],
      by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], le_refl _,
      by norm_num [modelData], fun _ => by norm_num [modelData], le_refl _, le_refl _, fun _ => ?_, by norm_num [modelData], le_refl _,
      le_refl _, ?_⟩
    · have : (1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 + 1 / 2) := Real.one_le_rpow hx (by norm_num)
      simpa [modelData] using this
    · have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      exact mul_nonneg (by norm_num [modelData]) hl2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]
  ·
    rw [hnT]
    norm_num [modelData]
  ·
    show (0 : ℝ) ≤ _
    have : (0 : ℝ) < (modelData (H := H)).x := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).b := by norm_num [modelData]
    positivity
  ·
    show (0 : ℝ) ≤ _
    have : (0 : ℝ) < (modelData (H := H)).x := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).b := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).k := by norm_num [modelData]
    positivity
  ·
    refine ⟨le_refl _, by positivity, by norm_num [modelData], by norm_num [modelData], by positivity, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · norm_num [modelData, aM]
    · rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> positivity
    · have : wM u0 j ρ = 2 ^ 60 := by unfold wM; rw [if_pos h]
      rw [this]
      norm_num [modelData]
    · have : wM u0 j ρ = 2 ^ 56 := by unfold wM; rw [if_neg h]
      rw [this]
      norm_num [modelData]
    · rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> norm_num [aM]
  ·
    rw [fPl_eq, cardHM]
    norm_num [modelData]
  ·
    rw [fPl_eq, cardHM]
    norm_num [modelData]
  · norm_num [modelData]
  · have : (65536 : ℝ) ^ (-((1 : ℝ) / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    rw [hcu, cardHM]
    show (65536 : ℝ) ^ (-((1 : ℝ) / 8)) * ((65536 : ℕ) : ℝ) / 2 ≤ ((65536 : ℕ) : ℝ)
    push_cast
    nlinarith
  · have : (65536 : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    rw [hcu, cardHM]
    show (65536 : ℝ) ^ (-(1 : ℝ)) ≤ ((65536 : ℕ) : ℝ) / ((65536 : ℕ) : ℝ)
    rw [div_self (by norm_num)]
    exact this
  · have : (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    show (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ ((1 : ℕ) : ℝ)
    simpa using this
  · have h3 : (65536 : ℝ) ^ (-1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    rw [Real.rpow_neg_one] at h3
    rw [cardHM]
    show (65536 : ℝ) ≤ ((65536 : ℕ) : ℝ) ^ 2 * (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1)
    push_cast
    have h4 : (65536 : ℝ) = 65536 ^ 2 * (65536 : ℝ)⁻¹ := by norm_num
    calc (65536 : ℝ) = 65536 ^ 2 * (65536 : ℝ)⁻¹ := h4
      _ ≤ 65536 ^ 2 * (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  ·
    intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (log_wM u0 j (ePM ρ)).1
  ·
    intro u0
    have hf : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin 1, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ 60 := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), (60 : ℝ) :=
        Finset.sum_le_sum fun ρ _ => (log_wM u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * 60) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 60 := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin 1))) fun j _ => h1 j
    simpa [CM, modelData] using h3
  · norm_num [modelData]
  · refine le_rpow_26 _ _ (by norm_num [modelData]) ?_
    have h1 : (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ (26 : ℝ) ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at h1
    show (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ 65536
    linarith [h1, (by norm_num : (26 : ℝ) ^ 3 ≤ 65536)]
  · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 65536)
    simpa [modelData] using this
  · norm_num [modelData, CM, KBig]
end Formalism.LFunctionChainParameters.LChain.Model
