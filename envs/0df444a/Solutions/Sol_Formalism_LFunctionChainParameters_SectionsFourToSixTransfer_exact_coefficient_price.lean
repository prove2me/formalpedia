-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.exact_coefficient_price
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:55.939985+00:00
-- url     : https://prove2.me/submissions/e0495a19-ab16-4503-9ffd-a1958a5fe14c

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_exact_coefficient_difference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : ExactCoeffPrice := by
  intro U0 W Top m f D bN hW u0
  have hd := exact_coefficient_difference D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hx0 : 0 < D.x := by linarith
  have hq0 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hr0 : 0 ≤ ((m : ℝ) - 1) / (2 * D.k) := div_nonneg (by linarith) (by linarith)
  have hr1 : ((m : ℝ) - 1) / (2 * D.k) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have t1 : (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π) ≤ D.L := by
    have := mul_nonneg hq0 hl0
    linarith
  have t2 : (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ 1 / 2 * D.L := by
    calc (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ (((m : ℝ) - 1) / (2 * D.k)) * D.L :=
          mul_le_mul_of_nonneg_left hl2 hr0
      _ ≤ 1 / 2 * D.L := mul_le_mul_of_nonneg_right hr1 (by linarith)
  have t3 : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg := mul_nonneg hq0 hlg
  have t4 : (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)) ≤ 1 := by
    have hterm : ∀ (ρ : Fin f) (j : Fin m), Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ) ≤ 1 / D.x := by
      intro ρ j
      obtain ⟨b0, w0, wb, _⟩ := hb u0 j ρ
      have h1x : 0 < 1 + 1 / D.x := by positivity
      have := Real.log_le_log w0 wb
      rw [Real.log_mul b0.ne' h1x.ne'] at this
      have := Real.log_le_sub_one_of_pos h1x
      linarith
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))
        ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 1 / D.x :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => hterm ρ j))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have e : 1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (1 / D.x))) = (m : ℝ) / D.x := by field_simp
    rw [e] at h5
    have : (m : ℝ) / D.x ≤ 1 := by rw [div_le_one hx0]; exact hmx
    linarith
  have t5 : (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ)) ≤ 2 * D.L := by
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 2 * D.L :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => (hb u0 j ρ).2.2.2))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / D.k)
    have e : 1 / D.k * (1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (2 * D.L)))) = (m : ℝ) / D.k * (2 * D.L) := by
      field_simp
    rw [e] at h6
    have h7 : (m : ℝ) / D.k ≤ 1 := by rw [div_le_one hk0]; exact hmk
    have h8 := mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ 2 * D.L)
    linarith
  linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
