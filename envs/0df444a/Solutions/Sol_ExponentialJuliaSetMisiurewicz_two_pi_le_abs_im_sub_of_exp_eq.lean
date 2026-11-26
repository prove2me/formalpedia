-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.two_pi_le_abs_im_sub_of_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:40.305388+00:00
-- url     : https://prove2.me/submissions/fc346d15-bd4f-493e-bead-bf76b49c7b97

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
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
theorem _root_.solution {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (hne : a ≠ b) :
    2 * Real.pi ≤ |a.im - b.im| := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hkne : k ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp only [Int.cast_zero, zero_mul, add_zero] at hk
    exact hne hk
  have him : a.im - b.im = (k : ℝ) * (2 * Real.pi) := by
    rw [hk]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re]
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs (by omega)
    have hcast : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := by push_cast; ring
    calc (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hk1
      _ = |(k : ℝ)| := hcast
  nlinarith [Real.pi_pos]
end ExponentialJuliaSetMisiurewicz
