-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.err_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:22.955764+00:00
-- url     : https://prove2.me/submissions/f7d3e431-f235-4998-b137-1aa5a72b0096

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
theorem _root_.solution {A c₃ Y Λ l : ℝ} (hc₃ : 0 < c₃) (hΛ : 0 < Λ) (hYΛ : l ^ 2 / 4 * Λ ≤ Y)
    (hYl : l ^ 2 / 4 ≤ Y)
    (hK1 : Real.log (4 * (|A| + 1)) ≤ c₃ * (l ^ 2 / 4))
    (hK2 : Real.log (4 * (|A| + 1)) ^ 2 ≤ c₃ * (l ^ 2 / 4)) :
    |A| * (Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y))) ≤ 1 / 2 := by
  set K := Real.log (4 * (|A| + 1)) with hK
  have hA1 : 0 < 4 * (|A| + 1) := by positivity
  have hK0 : 0 ≤ K := Real.log_nonneg (by linarith [abs_nonneg A])
  have hexpK : Real.exp (-K) = 1 / (4 * (|A| + 1)) := by
    rw [Real.exp_neg, Real.exp_log hA1, one_div]
  have hl : l ^ 2 / 4 ≤ Y / Λ := by
    rw [le_div_iff₀ hΛ]
    linarith
  have hc3l : c₃ * (l ^ 2 / 4) ≤ c₃ * Y / Λ := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hl hc₃.le
  have e1 : Real.exp (-(c₃ * Y / Λ)) ≤ Real.exp (-K) := Real.exp_le_exp.mpr (by linarith)
  have hsq : K ≤ Real.sqrt (c₃ * Y) := by
    have hKY : K ^ 2 ≤ c₃ * Y := by
      have : c₃ * (l ^ 2 / 4) ≤ c₃ * Y := mul_le_mul_of_nonneg_left hYl hc₃.le
      linarith
    have h := Real.sqrt_le_sqrt hKY
    rwa [Real.sqrt_sq hK0] at h
  have e2 : Real.exp (-Real.sqrt (c₃ * Y)) ≤ Real.exp (-K) := Real.exp_le_exp.mpr (by linarith)
  rw [hexpK] at e1 e2
  have hsum : Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y)) ≤ 2 / (4 * (|A| + 1)) := by
    have : 2 / (4 * (|A| + 1)) = 1 / (4 * (|A| + 1)) + 1 / (4 * (|A| + 1)) := by ring
    linarith
  calc |A| * (Real.exp (-(c₃ * Y / Λ)) + Real.exp (-Real.sqrt (c₃ * Y)))
      ≤ |A| * (2 / (4 * (|A| + 1))) := mul_le_mul_of_nonneg_left hsum (abs_nonneg A)
    _ ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hA1]
      nlinarith [abs_nonneg A]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
