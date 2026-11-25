-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:05.395597+00:00
-- url     : https://prove2.me/submissions/1b365c13-afca-47a3-99d3-c4b1be85a8d3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_integral_rpow_div_log
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_Fm_div_mul_log_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_intervalIntegrable_inv_log


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
theorem _root_.solution (K θ : ℝ) {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    Fm K θ β X / Real.log X + ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) =
      Fm K θ β 2 / Real.log 2 + K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) := by
  have hder : ∀ t ∈ Set.uIcc 2 X, HasDerivAt (fun t => Fm K θ β t / Real.log t)
      (K * (1 / Real.log t) - K * θ * (t ^ (β - 1) / Real.log t) - Fm K θ β t / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    have hp : HasDerivAt (fun t : ℝ => t ^ β) (β * t ^ (β - 1)) t := Real.hasDerivAt_rpow_const (Or.inl h0)
    have hF : HasDerivAt (fun t => Fm K θ β t) (K * (1 - θ * (β * t ^ (β - 1)) / β)) t := by
      unfold Fm
      exact (((hasDerivAt_id t).sub ((hp.const_mul θ).div_const β)).const_mul K)
    have := hF.div (Real.hasDerivAt_log h0) h1
    have hβ0 : β ≠ 0 := hβ.ne'
    refine HasDerivAt.congr_deriv (f := fun t => Fm K θ β t / Real.log t) this ?_
    generalize Fm K θ β t = F
    field_simp
  have hi1 : IntervalIntegrable (fun t => K * (1 / Real.log t)) MeasureTheory.volume 2 X :=
    (intervalIntegrable_inv_log le_rfl hX).const_mul K
  have hi2' : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t) MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    exact ((Real.continuousAt_rpow_const t (β - 1) (Or.inl h0)).div (Real.continuousAt_log h0) h1).continuousWithinAt
  have hi2 := hi2'.const_mul (K * θ)
  have hi3 := intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((hi1.sub hi2).sub hi3)
  rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_div_log hβ hX] at hftc
  have hli : ∫ t in (2 : ℝ)..X, 1 / Real.log t = liX X := rfl
  rw [hli] at hftc
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
