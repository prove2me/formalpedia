-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.ev_rpow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:00.224394+00:00
-- url     : https://prove2.me/submissions/0aa38d1f-6902-4ec0-a88d-799047e049be

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
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.ModelText
namespace Formalism.LFunctionChainParameters.LChain.ModelText
theorem _root_.solution (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in Filter.atTop, x ^ c ≤ Real.exp (x ^ δ) := by
  have hc : 0 < (|c| + 1)⁻¹ := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
  have hxpos : 0 < x := by linarith
  have h1 : (|c| + 1) * Real.log x ≤ x ^ δ := by
    have : (|c| + 1) * Real.log x ≤ (|c| + 1) * ((|c| + 1)⁻¹ * x ^ δ) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at this
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.2
  have hlog0 := Real.log_nonneg hx1
  have : Real.log x * c ≤ Real.log x * |c| := by gcongr; exact le_abs_self c
  nlinarith [abs_nonneg c]
end Formalism.LFunctionChainParameters.LChain.ModelText
