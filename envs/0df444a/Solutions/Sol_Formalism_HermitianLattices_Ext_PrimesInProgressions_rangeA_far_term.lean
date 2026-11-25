-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_far_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:40.914071+00:00
-- url     : https://prove2.me/submissions/1e85e774-cbd8-432d-aa96-cf3ea3788c63

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_cZ_pos


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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) (hM : 8 ≤ M) (y cA β : ℝ) (hy : 2 ≤ y) (hcA : cA ≤ cZ)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (hβ : 1 / 2 ≤ β)
    (hr : ¬ InRegion cZ M (β : ℂ)) :
    ‖(y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hy0 : 0 < y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log y := Real.mul_self_sqrt hL
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hZ := cZ_pos
  unfold InRegion at hr
  simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re, not_le] at hr
  set l := Real.log ((M : ℝ) * 2) with hl'
  have hl0 : 0 < l := Real.log_pos (by linarith)
  have hl2 : l ≤ 2 * Real.log M := by
    rw [hl', Real.log_mul (by linarith) (by norm_num)]
    have : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hl3 : l ≤ 2 * cZ * s := by nlinarith
  have h1 : cZ < (1 - β) * l := by
    have : cZ / l < 1 - β := by linarith
    rwa [div_lt_iff₀ hl0] at this
  have hb1 : 0 < 1 - β := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2 : s / 2 ≤ (1 - β) * Real.log y := by
    have h3 : cZ * s ≤ (1 - β) * (2 * cZ * s) * s := by
      have : (1 - β) * l ≤ (1 - β) * (2 * cZ * s) := mul_le_mul_of_nonneg_left hl3 hb1.le
      nlinarith
    have h4 : cZ * (s / 2) ≤ cZ * ((1 - β) * (s * s)) := by nlinarith
    rw [← hss]
    exact le_of_mul_le_mul_left h4 hZ
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < β)]
  have h5 : y ^ β = y * Real.exp (-((1 - β) * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    nth_rewrite 2 [← Real.exp_log hy0]
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : Real.exp (-((1 - β) * Real.log y)) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ (by linarith), h5]
  have h7 : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have : y * Real.exp (-((1 - β) * Real.log y)) ≤ y * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_left h6 hy0.le
  have h8 : 0 ≤ y * Real.exp (-(s / 2)) := by positivity
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
