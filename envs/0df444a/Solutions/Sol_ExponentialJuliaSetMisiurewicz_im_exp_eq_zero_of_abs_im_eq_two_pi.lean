-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.im_exp_eq_zero_of_abs_im_eq_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:42.315074+00:00
-- url     : https://prove2.me/submissions/06af3e69-7dc8-438c-b950-69aac2caa0a0

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (h : |z.im| = 2 * Real.pi) :
    (Complex.exp z).im = 0 := by
  rw [Complex.exp_im]
  rcases abs_eq (by positivity : (0 : ℝ) ≤ 2 * Real.pi) |>.mp h with h' | h'
  · rw [h', show (2 : ℝ) * Real.pi = ((2 : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, mul_zero]
  · rw [h', show -((2 : ℝ) * Real.pi) = ((-2 : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, mul_zero]
end ExponentialJuliaSetMisiurewicz
