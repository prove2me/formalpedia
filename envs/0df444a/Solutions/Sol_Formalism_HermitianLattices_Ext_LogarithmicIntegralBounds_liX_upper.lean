-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.liX_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:40.851449+00:00
-- url     : https://prove2.me/submissions/427ca67e-8c33-480f-86e1-cc473b49512c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
private lemma intervalIntegrable_inv_log_two {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 Y := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact (Real.log_pos (by linarith [ht.1])).ne'
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
