-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelEv.sizesOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:30:48.697831+00:00
-- url     : https://prove2.me/submissions/e342c298-2fbf-413e-ab7c-e451156cef2a

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_hostFacts_DA
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fPl_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fM_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_wE_cases
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_askDA_le

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
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
set_option maxHeartbeats 1600000
namespace Formalism.LFunctionChainParameters.LChain.ModelEv
theorem _root_.solution (x ε b : ℝ) (m N n : ℕ) (hcard : Fintype.card H = n)
    (hx : 3 ≤ x) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : x ≤ n) (hb : b = 12 * n * (x + 1) * x)
    (hm1 : x ^ ((1 : ℝ) / 2 - ε) ≤ m) (hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) (hmx : (m : ℝ) ≤ x)
    (hk : x * m ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) (hL : Real.log b ≤ 2 * x ^ ε) (hN : x * b ≤ N)
    (hl3 : 3 ≤ Real.log x) :
    SizesAt 1 1 2 ε x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hbx : x ≤ b := by
    rw [hb]
    have : 1 ≤ 12 * (n : ℝ) * (x + 1) := by nlinarith
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm1
  have hm1' : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hxe' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hnT : (DE (H := H) x ε b m N).nT = n := by
    unfold Data.nT
    rw [Fintype.card_coe, Finset.card_univ, hcard]
  have hcu : (univ : Finset H).card = n := by rw [Finset.card_univ, hcard]
  have hf : fPl H = 2 * (n : ℝ) := by rw [fPl_eq, hcard]
  have hlogw : ∀ (u0 : H) (j : Fin m) (ρ : E0 × H), 0 ≤ Real.log (wE m b u0 j ρ) ∧ Real.log (wE m b u0 j ρ) ≤ Real.log b := by
    intro u0 j ρ
    rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
    · exact ⟨hlb, le_refl _⟩
    · simpa using hlb
  refine ⟨H, inferInstance, inferInstance, inferInstance, (univ : Finset H), inferInstance, m, fM H,
    DE x ε b m N, CM, 0, DA, fun _ => 0, N, univ, univ, fun _ => x * b, wE m b, Equiv.refl _, ePM,
    0, x * b, 1 / (2 * fPl H * (x + 1) * x), rfl, rfl, le_refl _, le_refl _, le_refl _, hostFacts_DA,
    ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [DE], fun _ => rfl⟩, ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩, ?_, ?_, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hn1, hm2, le_refl _, by norm_num, ?_, ?_, ?_, hlb, hL, hlb, hL,
      zero_le_one, ?_, le_refl _, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, fun _ => ?_, by norm_num [DE], le_refl _, le_refl _, ?_⟩
    · show 1 ≤ x * m
      nlinarith
    · show x * m ≤ x ^ (2 : ℝ)
      rw [Real.rpow_two]
      nlinarith
    · show x * m ≤ x * b
      nlinarith
    · show x * m * 1 ≤ x * b
      nlinarith
    · show 0 ≤ x * b
      positivity
    · show 0 ≤ x * b
      positivity
    · show x * b ≤ 2 * (x * b)
      nlinarith [mul_pos hx0 hb0]
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
      positivity
    · show 0 ≤ ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
        / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      refine mul_nonneg ?_ hl2
      show 0 ≤ x * m - 3
      nlinarith
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]
  ·
    rw [hnT]
    show ((0 : ℝ) + 4 * Real.sqrt 0) * (x ^ CM.cHH * b) ≤ 1 * x ^ ε * ((n : ℝ) * (x * b))
    rw [Real.sqrt_zero]
    have : 0 ≤ 1 * x ^ ε * ((n : ℝ) * (x * b)) := by positivity
    simpa using this
  ·
    refine ⟨le_refl _, by positivity, zero_lt_one, ?_, by rw [hf]; positivity, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · show (1 : ℝ) * (x * b) ≤ x * b
      linarith
    · show |x * b / b - x| ≤ 1
      rw [mul_div_assoc, div_self hb0.ne']
      simp
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    · have : wE m b u0 j ρ = b := by unfold wE; rw [if_pos h]
      rw [this]
      exact ⟨le_refl _, by show b ≤ b + 0 + 1; linarith⟩
    · have : wE m b u0 j ρ = 1 := by unfold wE; rw [if_neg h]
      rw [this]
      show (1 : ℝ) ≤ 2 * 1
      norm_num
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
      · rw [mul_div_assoc, div_self hb0.ne']
        nlinarith
      · simpa using hN
  · rw [hf]; positivity
  ·
    show 2 * fPl H * (x + 1) * (1 / (2 * fPl H * (x + 1) * x)) ≤ 1 / x
    rw [hf]
    apply le_of_eq
    field_simp
  ·
    show 6 * fPl H * (x + 1) * (0 + 1) ≤ b / x
    rw [hf, hb]
    apply le_of_eq
    field_simp
    ring
  · show x * b ≤ 2 * x * b
    nlinarith [mul_pos hx0 hb0]
  · have : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-(ε / 8)) * (n : ℝ) / 2 ≤ (n : ℝ)
    nlinarith
  · have : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-ε) ≤ (n : ℝ) / (n : ℝ)
    rw [div_self hn0.ne']
    exact this
  · exact hm1
  · rw [hcard]
    exact hk
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (ePM ρ)).1
  · intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ CM.cCount * (m : ℝ) * Real.log b
    simpa [CM] using h3
  ·
    intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have hxb : 0 < x * b := by positivity
    have hA : (DE (H := H) x ε b m N).ASK u0 ≤ ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b := by
      refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ => askDA_le N (x * b) t _ hxb.le fun ρ => ?_
      rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    have hM : ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b ≤ (DE (H := H) x ε b m N).Main u0 := by
      unfold Data.Main
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => ?_
      show x * b ≤ x * b * (Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ))
      have hg := Real.eulerMascheroniConstant_lt_two_thirds
      have hlm : Real.log (x * b) = Real.log x + Real.log b := Real.log_mul hx0.ne' hb0.ne'
      have := h1 j
      have h5 : 1 ≤ Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) := by linarith
      calc x * b = x * b * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 hxb.le
    have hE : ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b = ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      ring
    have e1 : 0 ≤ CM.cDiv * (DE (H := H) x ε b m N).nT * (DE (H := H) x ε b m N).a * (DE (H := H) x ε b m N).La := by
      rw [hnT]
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).a = x * b := rfl
      have q3 : (DE (H := H) x ε b m N).La = Real.log b := rfl
      rw [q1, q2, q3]
      exact mul_nonneg (by positivity) hlb
    have e2 : 0 ≤ CM.cDiv * (m : ℝ) * ((DE (H := H) x ε b m N).B0 + (DE (H := H) x ε b m N).Nc)
        * (DE (H := H) x ε b m N).x ^ (CM.eDiv * (DE (H := H) x ε b m N).ε) := by
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).B0 = (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε := rfl
      have q3 : (DE (H := H) x ε b m N).Nc = ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
          / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε))) := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q3, q4]
      positivity
    have e3 : 0 ≤ (DE (H := H) x ε b m N).LoP CM := by
      unfold Data.LoP
      rw [hnT]
      have q1 : CM.cLoss = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).b = b := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q4]
      positivity
    linarith
end Formalism.LFunctionChainParameters.LChain.ModelEv
