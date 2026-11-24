-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.size_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:25.947391+00:00
-- url     : https://prove2.me/submissions/ee7d0f53-2ba8-4f67-8c4d-0f15ba2302df

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {c Y Λ : ℝ} (hc0 : 0 < c) (hY0 : 0 < Y) (h80 : 80 * Λ ≤ Y)
    (hlog : Real.log (320 / c) ≤ Y / 20) :
    4 * Real.exp (Y * (9 / 10)) ≤ c * Real.exp Y / (2 * Y * Real.exp Λ ^ 2) := by
  have hApos : 0 < Real.exp (Y / 40) := Real.exp_pos _
  have hDpos : 0 < Real.exp (Y * (9 / 10)) := Real.exp_pos _
  have hLpos : 0 < Real.exp Λ ^ 2 := pow_pos (Real.exp_pos _) 2
  have hY1 : Y ≤ 40 * Real.exp (Y / 40) := by
    have := Real.add_one_le_exp (Y / 40)
    linarith
  have hcB : 320 ≤ c * Real.exp (Y / 20) := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (div_pos (by norm_num) hc0), div_le_iff₀ hc0] at h
    linarith
  have hL : Real.exp Λ ^ 2 ≤ Real.exp (Y / 40) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have hexpY : Real.exp Y = Real.exp (Y * (9 / 10)) * Real.exp (Y / 20) * Real.exp (Y / 40) * Real.exp (Y / 40) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h1 : Y * Real.exp Λ ^ 2 ≤ 40 * Real.exp (Y / 40) * Real.exp (Y / 40) :=
    mul_le_mul hY1 hL hLpos.le (by linarith)
  have h2 : 8 * (Y * Real.exp Λ ^ 2) ≤ c * Real.exp (Y / 20) * (Real.exp (Y / 40) * Real.exp (Y / 40)) := by
    have h3 : 320 * (Real.exp (Y / 40) * Real.exp (Y / 40)) ≤ c * Real.exp (Y / 20) * (Real.exp (Y / 40) * Real.exp (Y / 40)) :=
      mul_le_mul_of_nonneg_right hcB (by positivity)
    linarith
  rw [le_div_iff₀ (mul_pos (mul_pos two_pos hY0) hLpos), hexpY]
  have h4 := mul_le_mul_of_nonneg_left h2 hDpos.le
  nlinarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
