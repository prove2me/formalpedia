-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.moveCostEv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:29:30.137197+00:00
-- url     : https://prove2.me/submissions/c60e4da1-5293-4eeb-8a86-44a7bec9ec77

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution (Cd CL ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) := by
  set A : ℝ := 4 * |Cd| + 15 + 12 * |CL| with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 (A ^ 4), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxA : A ^ 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ ((1 : ℝ) / 4) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyA : A ≤ y := by
    have h1 := Real.rpow_le_rpow (by positivity) hxA (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 : (A ^ 4) ^ ((1 : ℝ) / 4) = A := by
      have := Real.pow_rpow_inv_natCast hA0 (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at this ⊢
      exact this
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * y := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hy] at this
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog1 : Real.log (x + 1) ≤ 1 + Real.log x := by
    have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hCL : CL * Real.log x ≤ |CL| * (4 * y) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hlog0) (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
  have hyy : y * y ≤ x ^ ((1 : ℝ) / 2 + ε) := by
    rw [hy, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hCd : Cd ≤ |Cd| := le_abs_self Cd
  have hCd0 : 0 ≤ |Cd| := abs_nonneg Cd
  have h1 : moveCost x Cd CL ≤ A * y := by
    unfold moveCost
    have e1 : 4 * |Cd| ≤ 4 * |Cd| * y := by nlinarith
    have e2 : A * y = 4 * |Cd| * y + 15 * y + 12 * |CL| * y := by rw [hA]; ring
    rw [e2]
    nlinarith
  exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hyA (by linarith)) hyy)
end Formalism.LFunctionChainParameters.LChain
