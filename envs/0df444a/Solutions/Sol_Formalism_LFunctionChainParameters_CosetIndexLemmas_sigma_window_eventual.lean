-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.CosetIndexLemmas.sigma_window_eventual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:09.229906+00:00
-- url     : https://prove2.me/submissions/cc743fe0-65e1-4fc7-8998-7c303802c686

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_ev_exp

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
theorem _root_.solution : SgWindowEv := by
  intro ε cH C1 e hε hC1
  obtain ⟨x1, hx1, h1⟩ := ev_exp (8 * (C1 + 1) ^ 2) (e + 2 * cH) (1 / 2) ε (by norm_num) hε
  obtain ⟨x2, hx2, h2⟩ := ev_exp 16 cH 1 (ε / 8) one_pos (by positivity)
  refine ⟨max x1 x2, ?_⟩
  intro x f m T de e0 hx hf hm hT hlT hde he0
  have hxa := h1 x (le_trans (le_max_left _ _) hx)
  have hxb := h2 x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith [le_trans (le_max_left x1 x2) hx]
  have hS : 0 < x ^ (-cH) := Real.rpow_pos_of_pos hx0 _
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _

  have hTexp : Real.exp (1 / 2 * x ^ ε) ≤ T := by
    rw [← Real.le_log_iff_exp_le hT]
    nlinarith
  have hEpos : 0 < Real.exp (1 / 2 * x ^ ε) := Real.exp_pos _

  set y := x ^ (-cH) / (2 * (C1 + 1)) with hy
  have hy0 : 0 < y := by positivity
  have hxE : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (e + 2 * cH) = x ^ e / (x ^ (-cH)) ^ 2 := by
    rw [Real.rpow_add hx0, ← Real.rpow_natCast (x ^ (-cH)) 2, ← Real.rpow_mul hx0.le, div_eq_mul_inv,
      ← Real.rpow_neg hx0.le]
    congr 2; push_cast; ring
  have hde2 : de ≤ y ^ 2 := by
    have a1 : 2 * f / T ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by
      calc 2 * f / T ≤ 2 * x ^ e / T := by gcongr
        _ ≤ 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) := by gcongr
    have a2 : 2 * x ^ e / Real.exp (1 / 2 * x ^ ε) ≤ y ^ 2 := by
      rw [div_le_iff₀ hEpos]
      have : y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) = 2 * x ^ e := by
        rw [hsplit, hy]; field_simp; ring
      calc 2 * x ^ e = y ^ 2 * (8 * (C1 + 1) ^ 2 * x ^ (e + 2 * cH)) := this.symm
        _ ≤ y ^ 2 * Real.exp (1 / 2 * x ^ ε) := mul_le_mul_of_nonneg_left hxa (by positivity)
    linarith
  have hsq : Real.sqrt de ≤ y := Real.sqrt_le_iff.2 ⟨hy0.le, hde2⟩
  have p1 : C1 * Real.sqrt de ≤ x ^ (-cH) / 2 := by
    calc C1 * Real.sqrt de ≤ C1 * y := mul_le_mul_of_nonneg_left hsq hC1
      _ ≤ (C1 + 1) * y := by nlinarith
      _ = x ^ (-cH) / 2 := by rw [hy]; field_simp

  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; norm_num
  have p2 : 4 * Real.sqrt (2 * e0) ≤ x ^ (-cH) / 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    have b1 : Real.sqrt 2 * Real.sqrt e0 ≤ 2 * Real.exp (-(x ^ (ε / 8))) :=
      mul_le_mul hs2 he0 (Real.sqrt_nonneg _) (by norm_num)
    have b2 : 16 * Real.exp (-(x ^ (ε / 8))) ≤ x ^ (-cH) := by
      rw [Real.exp_neg, Real.rpow_neg hx0.le]
      have hc0 : 0 < x ^ cH := Real.rpow_pos_of_pos hx0 _
      have he0' : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
      rw [one_mul] at hxb
      rw [← div_eq_mul_inv, div_le_iff₀ he0', ← div_eq_inv_mul, le_div_iff₀ hc0]
      exact hxb
    linarith
  linarith
end Formalism.LFunctionChainParameters.CosetIndexLemmas
