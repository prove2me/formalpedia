-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.main_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:09.990022+00:00
-- url     : https://prove2.me/submissions/f0b5b5b5-6fd5-44a0-9447-3818a109831a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_exp_neg_le_one_sub_half
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_lower
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_sub_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {θ β η l X : ℝ} (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hl : l ≤ Real.log X) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * l) :
    X * η / (2 * Real.log X) ≤ liX X - θ * liX (X ^ β) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have h2 : 2 ≤ X ^ β := by
    calc (2 : ℝ) ≤ 4 := by norm_num
      _ = √16 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √X := Real.sqrt_le_sqrt hX
      _ = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
  have hXβ : X ^ β ≤ X := by
    calc X ^ β ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
      _ = X := Real.rpow_one X
  have hli := liX_nonneg h2
  rcases hη with h | h
  · have h1 := liX_lower (by linarith : 4 ≤ X)
    have h3 : X * η / (2 * Real.log X) ≤ X / (2 * Real.log X) := by
      gcongr
      nlinarith
    nlinarith
  · have h1 := liX_sub_ge h2 hXβ
    have hθ1 : θ ≤ 1 := (abs_le.1 hθ).2
    have h3 : liX X - liX (X ^ β) ≤ liX X - θ * liX (X ^ β) := by nlinarith
    have hw : η ≤ (1 - β) * Real.log X := h.trans (mul_le_mul_of_nonneg_left hl (by linarith))
    have he : X ^ β = X * Real.exp (-((1 - β) * Real.log X)) := by
      rw [Real.rpow_def_of_pos hX0]
      nth_rw 2 [← Real.exp_log hX0]
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-((1 - β) * Real.log X)) ≤ 1 - η / 2 :=
      (Real.exp_le_exp.2 (by linarith)).trans (exp_neg_le_one_sub_half hη0 hη1)
    have h4 : X * η / 2 ≤ X - X ^ β := by
      rw [he]
      nlinarith
    have h5 : X * η / (2 * Real.log X) ≤ (X - X ^ β) / Real.log X := by
      rw [show X * η / (2 * Real.log X) = (X * η / 2) / Real.log X by field_simp]
      gcongr
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
