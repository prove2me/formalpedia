-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ.T3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:39:30.881126+00:00
-- url     : https://prove2.me/submissions/0fee3376-9074-4d1a-801e-75a6a92b6e5a

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_SZ_rp
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_SZ_nT_bound
import Theorems.Thm_Formalism_landauIteratedDerivatives_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
theorem _root_.solution {x ε Y m n nT b : ℝ} (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hY' : x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) = Y := by
    rw [← rp hx0, ← rp hx0, hY]; ring_nf
  have hmY : m * x ^ ε * x ^ (ε / 8) ≤ Y := by
    rw [← hY']; gcongr
  have hnT' := nT_bound hx0 hnT
  have key : 2 * n * m * x ^ ε ≤ 4 * Y * nT := by
    have hme : 0 ≤ m * x ^ ε := by positivity
    have hnT0 : 0 ≤ nT := by nlinarith
    calc 2 * n * m * x ^ ε = 2 * n * (m * x ^ ε) := by ring
      _ ≤ 2 * (2 * nT * x ^ (ε / 8)) * (m * x ^ ε) := by gcongr
      _ = 4 * nT * (m * x ^ ε * x ^ (ε / 8)) := by ring
      _ ≤ 4 * nT * Y := by gcongr
      _ = 4 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc m * ((2 * n) * m * b * x ^ ε) = (2 * n * m * x ^ ε) * (m * b) := by ring
    _ ≤ (4 * Y * nT) * (m * b) := mul_le_mul_of_nonneg_right key hmb
    _ = 4 * Y * (nT * m * b) := by ring
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
