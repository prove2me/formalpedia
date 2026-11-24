-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.data_completion_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:34.050808+00:00
-- url     : https://prove2.me/submissions/0e61c699-f76e-4e53-b652-72b00c75f0fe

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_compl_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_compl_uF
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_compl_main

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
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution (D0 : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hx : 0 < D0.x) (hb : 0 < D0.b) (ha : 0 ≤ D0.a) (hb' : 0 ≤ D0.b') (hk : 1 ≤ D0.k) (hLa : 0 ≤ D0.La)
    (hB0 : 0 ≤ D0.B0) (hXpp : 0 ≤ Xpp) (hf : 0 < f) (haT : ∀ t, 0 ≤ D0.aT t) (hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ)
    (hC : 0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cSl1 ∧ 0 ≤ C.cLoss)
    (hS0 : ∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ))
    (hS1 : ∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L)
    (hTop : ∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C) :
    SizeData₂ (compl D0 C) C Xpp := by
  obtain ⟨cE, cH, cCount, cSlope, cSl1, cLoss⟩ := hC
  have hk0 : 0 < D0.k := by linarith
  have hnT : 0 ≤ D0.nT := by unfold Data.nT; positivity
  have hLoP : 0 ≤ D0.LoP C := by unfold Data.LoP; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact ⟨hx, hb, ha, hb', hk0, Real.pi_pos, hf, haT, hw, fun _ _ => one_pos, fun _ _ => Real.exp_pos _,
      fun _ _ => le_refl _, cSl1, one_pos, le_refl _, le_refl _, by norm_num [compl]⟩
  ·
    intro u0 u
    have h1 := hTop u0
    rw [compl_main] at h1
    have h2 : (compl D0 C).logOm = D0.gam - D0.LpL := by
      simp [Data.logOm, compl, Real.pi_ne_zero]
    rw [h2]
    simp only [compl, Real.log_exp, Data.nT] at h1 ⊢
    linarith
  ·
    intro u0 u
    have : 0 ≤ C.cE * (m : ℝ) * D0.B0 := by positivity
    simpa [compl, Data.Ee] using this
  ·
    intro u0 u u'
    have : 0 ≤ C.cH * (D0.nT * D0.a * D0.La + (m : ℝ) * D0.B0) := by positivity
    simpa [compl, Data.nT] using this
  ·
    intro u0 u
    refine ⟨?_, ?_, fun u' => ?_⟩
    · have h1 : 0 ≤ C.cCount * (D0.La + (m : ℝ) ^ 2 * D0.La / D0.k) := by positivity
      have h2 : ∀ y : ℝ, y * Real.pi / Real.pi = y := fun y => by field_simp
      simp only [compl, Real.log_exp, h2, mul_zero, add_zero]
      unfold sLog
      linarith
    · simpa [compl, sLog] using hS1 u0
    · have : 0 ≤ C.cCount * Real.log D0.k := mul_nonneg cCount (Real.log_nonneg hk)
      simpa [compl] using this
  ·
    intro u0 u
    have h1 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La * (1 + (m : ℝ) / D0.k) := by positivity
    have h2 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La := by positivity
    exact ⟨by simpa [compl, Data.nT] using h1, by simpa [compl, Data.nT] using h2⟩
  ·
    intro u0 u
    have h1 : 0 ≤ C.cSl1 * (m : ℝ) * D0.B0 := by positivity
    have hS := hS0 u0
    have h2 : 0 ≤ C.cSl1 * D0.nT * (m : ℝ) * (D0.a / D0.k + D0.b') * sLog D0 u0 :=
      mul_nonneg (by positivity) hS
    have h3 : 0 ≤ C.cSl1 * Xpp := by positivity
    constructor
    · simp only [compl, Data.Ee, Finset.sum_const_zero]
      linarith
    · simp only [Lo5, compl, Data.Ee, Finset.sum_const_zero, Real.log_exp, Data.nT] at h2 ⊢
      linarith
  ·
    intro u0
    have e : (compl D0 C).LoP C = D0.LoP C := rfl
    rw [e]
    exact ⟨by simp [compl], hLoP⟩
  ·
    intro u0 _ _ _ _ _ _ _
    rw [compl_uF, compl_alt]
    simp [compl]
  ·
    intro u0
    rw [compl_alt]
    refine ⟨?_, ?_, le_refl _⟩
    · have : 0 ≤ D0.x ^ C.cHH * D0.b := by positivity
      simpa [compl] using this
    · have : 0 < D0.x ^ C.cHH * D0.b := by positivity
      simpa [compl] using this
  ·
    intro u0
    simp [compl]
end Formalism.LFunctionChainParameters.LChain
