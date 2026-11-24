-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ.T4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:37.5858+00:00
-- url     : https://prove2.me/submissions/8c1b984e-7164-48d2-b267-c19d90bc0fde

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
theorem _root_.solution {x ε Y m n nT nT2 b k : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m) (hb : 0 ≤ b) (hε : 0 < ε)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 < n)
    (hnT2 : nT2 ≤ n) (hk0 : 0 ≤ k) (hk2 : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) :
    m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) ≤ 2 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have pne := Real.rpow_pos_of_pos hx0 (-ε)
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hneg : x ^ (-ε) * x ^ ε = 1 := by rw [← rp hx0]; simp
  have he : m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
      = (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) := by
    have h2 : x ^ ε = 1 / x ^ (-ε) := by rw [eq_div_iff pne.ne', mul_comm, hneg]
    rw [h2]; field_simp
  rw [he]
  have hA : nT2 * k * (x ^ ε * x ^ ε) / n ^ 2 ≤ n * x ^ ((1 : ℝ) / 2 + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have hxe : 0 ≤ x ^ ε * x ^ ε := by positivity
    have e2 : n * x ^ ((1 : ℝ) / 2 + ε) * n ^ 2 = n * (n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) * (x ^ ε * x ^ ε) := by
      rw [show (1 : ℝ) / 2 + ε = ((1 : ℝ) / 2 - ε) + ε + ε by ring, rp hx0, rp hx0]; ring
    rw [e2]
    have := mul_le_mul hnT2 hk2 hk0 hn.le
    exact mul_le_mul_of_nonneg_right this hxe
  have hnT' := nT_bound hx0 hnT
  have hXe : x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8) ≤ Y := by
    rw [← rp hx0, hY]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hB : n * x ^ ((1 : ℝ) / 2 + ε) ≤ 2 * Y * nT := by
    have hp := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 + ε)
    have hnT0 : 0 ≤ nT := by nlinarith
    calc n * x ^ ((1 : ℝ) / 2 + ε) ≤ (2 * nT * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε) :=
          mul_le_mul_of_nonneg_right hnT' hp.le
      _ = 2 * nT * (x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8)) := by ring
      _ ≤ 2 * nT * Y := by gcongr
      _ = 2 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) ≤ (m * b) * (n * x ^ ((1 : ℝ) / 2 + ε)) :=
        mul_le_mul_of_nonneg_left hA hmb
    _ ≤ (m * b) * (2 * Y * nT) := mul_le_mul_of_nonneg_left hB hmb
    _ = 2 * Y * (nT * m * b) := by ring
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
