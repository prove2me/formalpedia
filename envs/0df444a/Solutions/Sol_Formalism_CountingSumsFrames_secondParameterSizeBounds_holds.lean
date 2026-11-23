-- Prove2me | solution 1 for Formalism.CountingSumsFrames.secondParameterSizeBounds_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:21.345739+00:00
-- url     : https://prove2.me/submissions/d934b022-57ff-47b5-b8a4-ec93b0990813

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_basic
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_size
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_slack
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_floor
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_om

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
set_option maxHeartbeats 1000000
namespace Formalism.CountingSumsFrames
theorem _root_.solution : ParamsII0 := by
  intro CE C₂ hCE hC₂
  refine ⟨64 * CE + 400 + C₂, by linarith, ?_⟩
  intro p r N N₁ Nₛ J k n' L₁ G' Y a al c₀ c'' D cStar hH hal0 hal
  obtain ⟨hp13, hr2, hrN1, hN1, hrY, hClog, hk, h256, hCD, hDc, hCa, hL1, hLG, hNs1, hNs2,
    hJ, hJr⟩ := hH
  have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hrN1' : (r : ℝ) ≤ N₁ := by exact_mod_cast hrN1
  have hN1' : (N₁ : ℝ) ^ 2 ≤ r * N := by exact_mod_cast hN1
  have hk' : (N₁ : ℝ) + 3 * r ≤ k := by exact_mod_cast hk
  have hNs1' : (Nₛ : ℝ) ≤ N₁ := by exact_mod_cast hNs1
  have hNs2' : (Nₛ : ℝ) ≤ 2 * N := by exact_mod_cast hNs2
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr2' hrN1' hN1' hk'
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hNone' : 1 ≤ N := by exact_mod_cast hNone
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hQ1 : 1 ≤ QII p G' := one_le_pow₀ hp1
  have hpQ : (p : ℝ) ≤ QII p G' := by
    unfold QII
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp1 (by omega)
  have hom0 : (0 : ℝ) ≤ omII r N n' c₀ c'' := by unfold omII; positivity
  have hc1 : 1 ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have : (8 : ℝ) ≤ cStar := by exact_mod_cast (show 8 ≤ cStar by omega)
    linarith
  have hc0le : (c₀ : ℝ) ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have := pII0_om r N n' c₀ c'' (by omega) hNone'
    have : (0 : ℝ) ≤ cStar := Nat.cast_nonneg _
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  set Q := QII p G' with hQdef
  set c' := cPrII r N n' c₀ c'' cStar with hcdef
  set M := (k : ℝ) ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have hCa' : (64 * CE + 400 + C₂) * M ≤ a := by
    have : (64 * CE + 400 + C₂) * M
        = (64 * CE + 400 + C₂) * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y := by
      rw [hMdef]; ring
    linarith
  have ha0 : 0 ≤ a := le_trans (mul_nonneg (by linarith) hM0) hCa'
  refine ⟨?_, ?_, ?_, ?_, hY1, ?_⟩
  · unfold errorTerm mStarII
    have hs := pII0_size CE p r N N₁ Nₛ k Q c' Y al (by linarith) (Nat.cast_nonneg _) hpQ hQ1
      hr2' hrN1' hN1' hk' (Nat.cast_nonneg _) hNs1' hNs2' hc1 hY0 hal0 hal
    have : 32 * (2 * CE + 7) * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    linarith
  · intro B hB
    unfold slII mStarII
    have hs := pII0_slack r N N₁ k Q c' Y al c₀ hQ1 hr2' hrN1' hN1' hk' hc1 hY0 hal0 hal
      (Nat.cast_nonneg _) hc0le
    have h155 : 155 * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have hYk : 100 ≤ Y * (k : ℝ) ^ 2 := by
      have : (64 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact pII0_floor _ Y k Q a B (by linarith) ha0 hYk (by linarith) hB
  · have : (0 : ℝ) ≤ (k : ℝ) ^ 2 * Y ^ 2 := by positivity
    nlinarith
  · rcases le_or_gt 0 (Real.log a) with hl | hl
    · have hsq : (Nₛ : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNs1' 2
      have e1 : C₂ * (Nₛ : ℝ) ^ 2 ≤ (64 * CE + 400 + C₂) * (N₁ : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hsq (by positivity) (by linarith)
      have e2 := mul_le_mul_of_nonneg_right e1 hl
      linarith
    · have : C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hl.le
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
  · omega
end Formalism.CountingSumsFrames
