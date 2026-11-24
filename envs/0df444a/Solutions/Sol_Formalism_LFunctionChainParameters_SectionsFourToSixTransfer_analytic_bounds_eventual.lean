-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.analytic_bounds_eventual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:52.756247+00:00
-- url     : https://prove2.me/submissions/392280fe-b067-4c8a-b278-901b603059af

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_text_key

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
set_option maxHeartbeats 1000000
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : ExponentialPowerWindows := by
  intro ε e hε he
  obtain ⟨x₀, h⟩ := text_key ε (4 * e + 2) hε
  refine ⟨x₀, ?_⟩
  intro x k fR mR nT N Sc lrd v hx hk1 hk hf1 hf hm1 hm hN1 hN hn1 hSc0 hSc hv hlv hlrd
  obtain ⟨hx8, hlb, hb, ha, hbp, hK⟩ := h x hx
  have hxp : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 64 ≤ x ^ 2 := by nlinarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have h8x : 8 * x ≤ x ^ 2 := by nlinarith
  set y := x ^ e with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 he
  have hE : x ^ (4 * e + 2) = y ^ 4 * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hy,
      ← Real.rpow_natCast (x ^ e) 4, ← Real.rpow_mul hxp.le]
    congr 2
    push_cast; ring
  rw [hE] at hK
  have hk0 : 0 < k := by linarith
  have hf0 : 0 < fR := by linarith
  have hm0 : 0 < mR := by linarith
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := by linarith
  have y2 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y3 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y1 : y ≤ y ^ 4 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 4)
  have y4 : 0 < y ^ 4 := by positivity
  have big : ∀ {K c : ℝ}, K ≤ c * y ^ 4 → c ≤ x ^ 2 → K ≤ y ^ 4 * x ^ 2 := by
    intro K c h1 h2
    have := mul_le_mul_of_nonneg_right h2 y4.le
    linarith
  have p2 : fR * k ≤ y ^ 2 := by
    have : fR * k ≤ y * y := mul_le_mul hf hk hk0.le hy0.le
    linarith [sq y]
  have pm2 : mR * k ≤ y ^ 2 := by
    have : mR * k ≤ y * y := mul_le_mul hm hk hk0.le hy0.le
    linarith [sq y]
  have pmN : mR * N ≤ y ^ 2 := by
    have : mR * N ≤ y * y := mul_le_mul hm hN hN0.le hy0.le
    linarith [sq y]
  have p3 : fR * k ^ 2 ≤ y ^ 3 := by
    have : fR * k * k ≤ y ^ 2 * y := mul_le_mul p2 hk hk0.le (by positivity)
    have e1 : fR * k ^ 2 = fR * k * k := by ring
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have pmNk : mR * N * k ≤ y ^ 3 := by
    have : mR * N * k ≤ y ^ 2 * y := mul_le_mul pmN hk hk0.le (by positivity)
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have p4 : fR * (mR * N * k) ≤ y ^ 4 := by
    have : fR * (mR * N * k) ≤ y * y ^ 3 := mul_le_mul hf pmNk (by positivity) hy0.le
    have e2 : y ^ 4 = y * y ^ 3 := by ring
    linarith
  obtain ⟨A1, _, A3⟩ := hK k hk0 (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, B2, _⟩ := hK (2 * (fR * k)) (by positivity) (big (c := 2) (by linarith) (by linarith))
  obtain ⟨C1, _, _⟩ := hK (fR * k ^ 2) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨D1, _, _⟩ := hK (fR * (mR * N * k)) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, E2, _⟩ := hK (mR * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨F1, _, _⟩ := hK (mR * N * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨G1, _, _⟩ := hK (8 * x * fR) (by positivity) (by
    have := mul_le_mul h8x (le_trans hf y1) hf0.le (by positivity)
    linarith)
  obtain ⟨H1, _, _⟩ := hK (x * (mR * N)) (by positivity) (by
    have := mul_le_mul hxx (le_trans pmN y2) (by positivity) (by positivity)
    linarith)
  obtain ⟨_, I2, _⟩ := hK (x * mR) (by positivity) (by
    have := mul_le_mul hxx (le_trans hm y1) hm0.le (by positivity)
    linarith)
  have hax : aTx x ε = x * bTx x ε := rfl
  have hna : aTx x ε ≤ nT * aTx x ε := le_mul_of_one_le_left ha.le hn1
  have hak : 0 < aTx x ε / k := div_pos ha hk0
  have hlk : Real.log k ≤ Real.log (aTx x ε) := Real.log_le_log hk0 A1
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.log_mul hk0.ne' hv.ne']; linarith
  · rw [Real.log_mul ha.ne' hv.ne']; linarith
  · have : Real.log (bTx x ε) ≤ Real.log (aTx x ε) := Real.log_le_log hb (by rw [hax]; exact le_mul_of_one_le_left hb.le hx1)
    linarith
  · rw [hlb]; exact Real.one_le_rpow hx1 hε.le
  · have : fR * k * (bpTx x ε + Sc) ≤ fR * k * (bpTx x ε + bpTx x ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · exact le_trans (le_mul_of_one_le_left hk0.le hx1) A3
  · have : fR * mR * N ≤ aTx x ε / k := by rw [le_div_iff₀ hk0]; linarith
    exact le_trans this (le_mul_of_one_le_left hak.le hn1)
  · rw [le_div_iff₀ hk0]; linarith
  · rw [le_div_iff₀ hk0]; linarith
  · rw [hax] at G1
    have : x * (8 * fR) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp
  · rw [hax] at H1
    exact le_of_mul_le_mul_left H1 hxp
  · rw [hax] at I2
    have : x * (mR * bpTx x ε) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
