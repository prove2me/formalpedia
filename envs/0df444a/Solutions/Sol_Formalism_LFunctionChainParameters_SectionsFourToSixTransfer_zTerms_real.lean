-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.zTerms_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:44.419206+00:00
-- url     : https://prove2.me/submissions/2a6f4a9b-895d-41be-99bc-d2b6b7750ea0

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered

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
theorem _root_.solution {cZ cL cU a k mR b' Sc L La lk lkv LZ fR nT sA logT : ℝ}
    (hcZ : 0 ≤ cZ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (ha : 0 ≤ a) (hk : 1 ≤ k) (hmk : mR ≤ k)
    (hb' : 0 ≤ b') (hSc : 0 ≤ Sc) (hL : 0 ≤ L) (hLLa : L ≤ La) (hlk : lk ≤ La) (hlkv : lkv ≤ La)
    (hLZ : LZ ≤ cL * La) (hw1 : fR * k * (b' + Sc) ≤ nT * a) (hw2 : fR * k ^ 2 ≤ nT * a)
    (hn : 0 ≤ nT) (hf : 0 ≤ fR) (hm : 0 ≤ mR) (hs0 : 0 ≤ sA) (hs1 : sA ≤ nT * (2 * a / k))
    (hT : logT ≤ cU * mR * L) :
    sA * logT ≤ 2 * cU * (nT * a * La * (mR / k)) ∧
    cZ * nT * a * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * k * (b' + Sc) * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * Sc * logT ≤ cZ * cU * (nT * a * La * (mR / k)) ∧
    cZ * fR * k ^ 2 * LZ ≤ cZ * cL * (nT * a * La) ∧
    cZ * nT * a * lkv ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * (k * lkv) ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * logT ≤ cZ * cU * (nT * a * La) := by
  have hk0 : 0 < k := by linarith
  have hLa : 0 ≤ La := le_trans hL hLLa
  have hna : 0 ≤ nT * a := mul_nonneg hn ha
  have hbS : 0 ≤ b' + Sc := add_nonneg hb' hSc
  have hmk' : 0 ≤ mR / k := div_nonneg hm hk0.le
  have hT' : logT ≤ cU * (mR * La) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLLa hm) hcU
    linarith
  have hcmL : 0 ≤ cU * (mR * La) := mul_nonneg hcU (mul_nonneg hm hLa)
  have hfkb : 0 ≤ fR * k * (b' + Sc) := mul_nonneg (mul_nonneg hf hk0.le) hbS
  have hfb : 0 ≤ fR * (b' + Sc) := mul_nonneg hf hbS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc sA * logT ≤ sA * (cU * (mR * La)) := mul_le_mul_of_nonneg_left hT' hs0
      _ ≤ nT * (2 * a / k) * (cU * (mR * La)) := mul_le_mul_of_nonneg_right hs1 hcmL
      _ = 2 * cU * (nT * a * La * (mR / k)) := by ring
  · have := mul_le_mul_of_nonneg_left hlk (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlk hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have hfS : 0 ≤ fR * Sc := mul_nonneg hf hSc
    have h1 := mul_le_mul_of_nonneg_left hT' hfS
    have h2 : fR * Sc * k ≤ nT * a := by
      have := mul_nonneg (mul_nonneg hf hk0.le) hb'
      linarith
    have h3 : fR * Sc * (cU * (mR * La)) = cU * ((fR * Sc * k) * (La * (mR / k))) := by
      field_simp
    have h4 : (fR * Sc * k) * (La * (mR / k)) ≤ nT * a * (La * (mR / k)) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg hLa hmk')
    have h5 := mul_le_mul_of_nonneg_left h4 hcU
    have h6 : fR * Sc * logT ≤ cU * (nT * a * (La * (mR / k))) := by linarith
    have := mul_le_mul_of_nonneg_left h6 hcZ
    linarith
  · have hfk : 0 ≤ fR * k ^ 2 := mul_nonneg hf (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hLZ hfk
    have h2 := mul_le_mul_of_nonneg_right hw2 (mul_nonneg hcL hLa)
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have := mul_le_mul_of_nonneg_left hlkv (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlkv hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hT' hfb
    have h2 : fR * (b' + Sc) * mR ≤ nT * a := by
      have := mul_le_mul_of_nonneg_left hmk hfb
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hcU hLa)
    have h4 : fR * (b' + Sc) * logT ≤ cU * (nT * a * La) := by linarith
    have := mul_le_mul_of_nonneg_left h4 hcZ
    linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
