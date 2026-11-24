-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.liX_two_rpow_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:29.773652+00:00
-- url     : https://prove2.me/submissions/165fe0f4-cc74-4f10-9b68-a7925be52e9c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {β : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) : |liX ((2 : ℝ) ^ β)| ≤ 4 := by
  unfold liX
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
  have h2 : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
  have h3 : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := (2 : ℝ) ^ β)
    (f := fun t => 1 / Real.log t) (C := 4) ?_
  · rw [Real.norm_eq_abs] at this
    calc _ ≤ 4 * |(2 : ℝ) ^ β - 2| := this
      _ ≤ 4 * 1 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 4 := by norm_num
  · intro t ht
    rw [Set.uIoc_of_ge h2] at ht
    have hl : Real.log 2 / 2 ≤ Real.log t := by
      have : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.log t := Real.log_le_log (by positivity) (by linarith [ht.1])
      rw [Real.log_rpow (by norm_num)] at this; linarith
    have hl2 := Real.log_two_gt_d9
    have hl3 : 0 < Real.log t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hl3]
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
