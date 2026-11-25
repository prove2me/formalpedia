-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_kernel_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:26.755621+00:00
-- url     : https://prove2.me/submissions/0b4b159c-d95f-46c3-98a5-933d102785f1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_norm_exp_sub_one_le_of_re_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (y η : ℝ) (hy : 0 < y) (hη : 0 ≤ η) (hη1 : η ≤ 1) (w : ℂ) (hw0 : 0 ≤ w.re)
    (hw2 : w.re ≤ 2) :
    ‖((y * (1 + η) : ℝ) : ℂ) ^ w - (y : ℂ) ^ w‖ ≤ 4 * η * ‖w‖ * y ^ w.re := by
  have hy1 : (0 : ℝ) < 1 + η := by linarith
  have hL0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have hLη : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos hy1
    linarith
  have hL2 : Real.log (1 + η) ≤ Real.log 2 := Real.log_le_log hy1 (by linarith)
  have hsplit : ((y * (1 + η) : ℝ) : ℂ) ^ w = (y : ℂ) ^ w * ((1 + η : ℝ) : ℂ) ^ w := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hy.le hy1.le w
  have hpow : ((1 + η : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log (1 + η) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy1.ne'), ← Complex.ofReal_log hy1.le, mul_comm]
  have hre : 0 ≤ (w * (Real.log (1 + η) : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hw0 hL0
  have hb := norm_exp_sub_one_le_of_re_nonneg _ hre
  have hre' : (w * (Real.log (1 + η) : ℂ)).re = w.re * Real.log (1 + η) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hnorm : ‖w * (Real.log (1 + η) : ℂ)‖ = ‖w‖ * Real.log (1 + η) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hexp : Real.exp (w.re * Real.log (1 + η)) ≤ 4 := by
    have h4 : Real.exp (2 * Real.log 2) = 4 := by
      rw [two_mul, Real.exp_add, Real.exp_log two_pos]; norm_num
    rw [← h4]
    apply Real.exp_le_exp.mpr
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  rw [hre', hnorm] at hb
  have hyw : ‖(y : ℂ) ^ w‖ = y ^ w.re := Complex.norm_cpow_eq_rpow_re_of_pos hy w
  have hypos : 0 ≤ y ^ w.re := Real.rpow_nonneg hy.le _
  rw [hsplit, hpow, ← mul_sub_one, norm_mul, hyw]
  calc y ^ w.re * ‖Complex.exp (w * (Real.log (1 + η) : ℂ)) - 1‖
      ≤ y ^ w.re * (Real.exp (w.re * Real.log (1 + η)) * (‖w‖ * Real.log (1 + η))) := by gcongr
    _ ≤ y ^ w.re * (4 * (‖w‖ * η)) := by
        gcongr
    _ = 4 * η * ‖w‖ * y ^ w.re := by ring
end Formalism.HermitianLattices.Ext.BoxTail
