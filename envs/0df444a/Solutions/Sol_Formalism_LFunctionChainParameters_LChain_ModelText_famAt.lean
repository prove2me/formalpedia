-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.famAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:32.792715+00:00
-- url     : https://prove2.me/submissions/975f50be-52f6-41d4-bba0-fe87d1116339

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_hostFacts_DA
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fPl_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_fM_pos

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
open Formalism.LFunctionChainParameters.LChain.ModelText
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.ModelText
theorem _root_.solution (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hx : 3 ≤ x)
    (hT : 1 ≤ x ∧ 1 ≤ bTx x ε ∧ Real.log (bTx x ε) = x ^ ε ∧ Real.log (aTx x ε) + x ^ (ε / 3) ≤ 2 * x ^ ε ∧
      kTx x ε ≤ aTx x ε ∧ 0 ≤ bpTx x ε ∧ kTx x ε * bpTx x ε ≤ aTx x ε ∧
      0 ≤ XppTx x ε (Fintype.card H) ∧ XppTx x ε (Fintype.card H) ≤ aTx x ε)
    (hnlo : x ^ (2 + 8 * ε) ≤ (Fintype.card H : ℝ))
    (hmlo : x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m) (hmhi : (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16))
    (h2 : 2 ≤ x ^ (9 * ε / 16))
    (hTT : x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 ≤ TT.card)
    (hT2 : x ^ (-ε) * (Fintype.card H : ℝ) ≤ T2.card)
    (hc1 : 2 * (2 * (Fintype.card H : ℝ)) * (x + 1) * thTx x ε ≤ 1 / x)
    (hc2 : 6 * (2 * (Fintype.card H : ℝ)) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x)
    (hw1 : 1 ≤ wppTx x ε (Fintype.card H)) : AllSizes x ε m TT T2 := by
  obtain ⟨hx1, hb1, hlogb, hLa, hka, hbp0, hkbp, hX0, hXa⟩ := hT
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := by linarith
  have ha : aTx x ε = x * bTx x ε := rfl
  have ha0 : 0 < aTx x ε := by rw [ha]; positivity
  have hab : bTx x ε ≤ aTx x ε := by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1
  have hXp0 : 0 < XpTx x ε := Real.exp_pos _
  have hbp : 0 < bpTx x ε := div_pos ha0 hXp0
  have hn0 : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hxe1 : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε0.le
  have hk_x : x ≤ kTx x ε := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)
    rwa [Real.rpow_one] at this
  have hk0 : 0 < kTx x ε := by linarith
  have heta0 : 0 < etaTx x ε := Real.exp_pos _
  have hetab : etaTx x ε ≤ bTx x ε :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hbpb : bpTx x ε ≤ bTx x ε := by
    have h1 : x * bpTx x ε ≤ x * bTx x ε := le_trans (mul_le_mul_of_nonneg_right hk_x hbp.le) hkbp
    exact le_of_mul_le_mul_left h1 hx0
  have hwpp0 : 0 < wppTx x ε (Fintype.card H) := by linarith
  have hwppbp : wppTx x ε (Fintype.card H) ≤ bpTx x ε := by
    unfold wppTx
    exact div_le_self hbp.le (by nlinarith)
  have hnT : (textData x ε m TT T2).nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_coe]
  have hTTpos : (0 : ℝ) < TT.card := lt_of_lt_of_le (by positivity) hTT
  have hTT1 : (1 : ℝ) ≤ TT.card := by
    have : 0 < TT.card := by exact_mod_cast hTTpos
    exact_mod_cast this
  have hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    have e : x ^ ((1 : ℝ) / 2 + ε / 2) = x ^ (9 * ε / 16) * x ^ ((1 : ℝ) / 2 - ε / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [e]
    exact hmhi.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _))
  have hxm : x * m ≤ kTx x ε := by
    have h1 : x * m ≤ x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2) := by
      rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hm_hi hx0.le
    rw [← Real.rpow_add hx0] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

  have hw : ∀ u0 j ρ, wppTx x ε (Fintype.card H) ≤ wF x ε m TT T2 u0 j ρ ∧ wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε := by
    intro u0 j ρ
    unfold wF
    split_ifs
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  have hlogw : ∀ u0 j ρ, 0 ≤ Real.log (wF x ε m TT T2 u0 j ρ) ∧ Real.log (wF x ε m TT T2 u0 j ρ) ≤ 2 * x ^ ε := by
    intro u0 j ρ
    obtain ⟨h1, h2'⟩ := hw u0 j ρ
    refine ⟨Real.log_nonneg (by linarith), ?_⟩
    have h3 := Real.log_le_log (by linarith) h2'
    rw [Real.log_mul (by norm_num) hb0.ne', hlogb] at h3
    have h4 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hf : (0 : ℝ) < (Model.fM H : ℝ) := by exact_mod_cast Model.fM_pos
  refine ⟨Model.hostFacts_DA, ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [textData], fun _ => rfl⟩, ⟨?_, ?_⟩,
    ⟨le_refl _, le_refl _⟩, ?_, ⟨?_, ?_⟩, ⟨?_, hTT, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hTT1, hm_hi, hxm, by norm_num, by
      show (1 : ℝ) ≤ kTx x ε
      linarith, ?_, hka, Real.rpow_nonneg hx0.le _, ?_, ?_, hLa, hbp0, hkbp, hX0, hXa, fun _ => ⟨ha0.le, ?_⟩, ?_, ?_,
      fun _ => ?_, by show (0 : ℝ) ≤ 1 / 2; norm_num, Real.rpow_nonneg hx0.le _, le_refl _, ?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    · show x ^ ε ≤ 2 * x ^ ε
      linarith
    · show 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ aTx x ε)
      have := Real.rpow_nonneg hx0.le (ε / 3)
      linarith
    · show aTx x ε ≤ 2 * aTx x ε
      linarith
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
      positivity
    · show 0 ≤ (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      exact mul_nonneg (by show 0 ≤ kTx x ε - 3; linarith) (Real.log_nonneg (by norm_num))
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CF]
  ·
    rw [hnT]
    show (x ^ (-1 : ℝ) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * bTx x ε) ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε)
    rw [Real.sqrt_zero, mul_zero, add_zero, ← mul_assoc, ← Real.rpow_add hx0]
    norm_num
    have h1 : aTx x ε ≤ (TT.card : ℝ) * aTx x ε := le_mul_of_one_le_left ha0.le hTT1
    have h3 : (TT.card : ℝ) * aTx x ε ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  ·
    refine ⟨heta0.le, hXp0, hbp, ?_, (Real.exp_pos _).le, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · have : bpTx x ε * XpTx x ε = aTx x ε := div_mul_cancel₀ _ hXp0.ne'
      rw [this, ha]
    · have : aTx x ε / bTx x ε = x := by rw [ha]; field_simp
      rw [this]; simp
    · linarith [(hw u0 j ρ).1]
    · have : wF x ε m TT T2 u0 j ρ = bTx x ε + etaTx x ε := by unfold wF; rw [if_pos h]
      rw [this]
      constructor <;> linarith
    · unfold wF
      rw [if_neg h]
      split_ifs
      · exact le_refl _
      · linarith
    · have h1 : aTx x ε / wF x ε m TT T2 u0 j ρ ≤ aTx x ε / wppTx x ε (Fintype.card H) :=
        div_le_div_of_nonneg_left ha0.le hwpp0 (hw u0 j ρ).1
      exact h1.trans (Nat.le_ceil _)
  · rw [Model.fPl_eq]; exact hc1
  · rw [Model.fPl_eq]; exact hc2
  · rw [ha]; nlinarith [mul_pos hx0 hb0]
  · rw [le_div_iff₀ hn0]; exact hT2
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hmlo
  · have h1 : (x ^ (2 + 8 * ε)) ^ 2 ≤ (Fintype.card H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hnlo 2
    have h3 : kTx x ε ≤ (x ^ (2 + 8 * ε)) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := by
      rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact h3.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _))
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (Model.ePM ρ)).1
  · intro u0
    have h1 : ∀ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
        ≤ 2 * x ^ ε := by
      intro j
      have h2' : ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ ∑ _ρ : Fin (Model.fM H), 2 * x ^ ε :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (Model.ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2'
      calc (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ (1 / (Model.fM H : ℝ)) * ((Model.fM H : ℝ) * (2 * x ^ ε)) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = 2 * x ^ ε := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ (2 : ℝ) * (m : ℝ) * x ^ ε
    linarith
end Formalism.LFunctionChainParameters.LChain.ModelText
