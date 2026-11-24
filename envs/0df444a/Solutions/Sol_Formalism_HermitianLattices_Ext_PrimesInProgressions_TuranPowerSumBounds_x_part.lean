-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.x_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.007409+00:00
-- url     : https://prove2.me/submissions/33c2c194-e598-4828-870a-f0bdb18b465b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_log_rr_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_rr_gt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_log


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (c₁ K : ℝ) (hc₁ : 0 < c₁) (j : ℕ) (hj : (j : ℝ) ≤ 2 * th a * K + j0 a) :
    c₁ * Real.exp (-K) ≤ c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j := by
  have hlog := log_rr_pos a
  have hid := th_log a
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  have hRj : rr a ^ j = Real.exp (j * Real.log (rr a)) := by
    rw [Real.exp_nat_mul, Real.exp_log hRpos]
  rw [hRj, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left ?_ hc₁.le
  rw [Real.exp_le_exp]
  have h1 : (j : ℝ) * Real.log (rr a)
      ≤ (2 * th a * K + j0 a) * Real.log (rr a) :=
    mul_le_mul_of_nonneg_right hj hlog.le
  have h2 : (2 * th a * K + j0 a) * Real.log (rr a)
      = K + j0 a * Real.log (rr a) := by
    linear_combination K * hid
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
