-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.mem_exp_exp_ball_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:45.613274+00:00
-- url     : https://prove2.me/submissions/d7cb2718-840d-4afc-8f58-0da0bdf0aa84

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {w : ℂ} (hw : w ≠ 0) {M x : ℝ}
    (hwM : |Real.log ‖w‖| ≤ M) (hx : M + 2 * Real.pi ≤ x) :
    w ∈ expIterate 2 '' ball (x : ℂ) 8 := by
  -- Choose a logarithm of w with imaginary part between exp x and exp x + 2π.
  let k : ℤ := ⌈(Real.exp x - (Complex.log w).im) / (2 * Real.pi)⌉
  let t : ℂ := Complex.log w + (k : ℂ) * (2 * Real.pi * Complex.I)
  have hp : 0 < 2 * Real.pi := by positivity
  have htim : t.im = (Complex.log w).im + (k : ℝ) * (2 * Real.pi) := by
    simp [t, Complex.mul_re, Complex.mul_im]
  have htre : t.re = Real.log ‖w‖ := by simp [t, Complex.log_re]
  have htlo : Real.exp x ≤ t.im := by
    have h := (div_le_iff₀ hp).mp
      (Int.le_ceil ((Real.exp x - (Complex.log w).im) / (2 * Real.pi)))
    rw [htim]
    change Real.exp x ≤ (Complex.log w).im + (k : ℝ) * (2 * Real.pi)
    linarith
  have hthi : t.im < Real.exp x + 2 * Real.pi := by
    have h := (mul_lt_mul_of_pos_right
      (Int.ceil_lt_add_one ((Real.exp x - (Complex.log w).im) / (2 * Real.pi))) hp)
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] at h
    rw [htim]
    change (Complex.log w).im + (k : ℝ) * (2 * Real.pi) < _
    linarith
  have htpos : 0 < t.im := (Real.exp_pos x).trans_le htlo
  have htne : t ≠ 0 := by
    intro h
    simp [h] at htpos
  -- Taking one further logarithm puts its real part between x and x + 1.
  have hnormlo : Real.exp x ≤ ‖t‖ := htlo.trans (Complex.im_le_norm t)
  have hnormhi : ‖t‖ ≤ Real.exp (x + 1) := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im t
    rw [htre, abs_of_pos htpos] at hnorm
    have hmx : M + 2 * Real.pi ≤ Real.exp x :=
      hx.trans (le_trans (by linarith : x ≤ x + 1) (Real.add_one_le_exp x))
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [Real.exp_add]
    have hmul := mul_le_mul_of_nonneg_left htwo (le_of_lt (Real.exp_pos x))
    linarith
  have hrelo : x ≤ Real.log ‖t‖ := by
    simpa using Real.log_le_log (Real.exp_pos x) hnormlo
  have hrehi : Real.log ‖t‖ ≤ x + 1 := by
    simpa using Real.log_le_log (norm_pos_iff.mpr htne) hnormhi
  -- Its imaginary part is bounded by π, placing the two-step preimage in the desired disk.
  refine ⟨Complex.log t, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (Complex.log t - (x : ℂ))
    simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
      Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero] at hnorm
    rw [abs_of_nonneg (sub_nonneg.mpr hrelo)] at hnorm
    linarith [Complex.abs_arg_le_pi t, Real.pi_lt_four]
  · have hexpt : Complex.exp t = w := by
      calc
        Complex.exp t = Complex.exp (Complex.log w) := by
          apply Complex.exp_eq_exp_iff_exists_int.mpr
          exact ⟨k, rfl⟩
        _ = w := Complex.exp_log hw
    simpa only [expIterate_succ, expIterate_zero, Complex.exp_log htne] using hexpt
end ExponentialJuliaSetMisiurewicz
