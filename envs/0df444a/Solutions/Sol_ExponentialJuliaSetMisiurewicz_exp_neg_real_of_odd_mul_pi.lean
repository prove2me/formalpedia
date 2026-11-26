-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exp_neg_real_of_odd_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:10.763021+00:00
-- url     : https://prove2.me/submissions/821a562a-b711-460b-90e9-dc52d4942890

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
theorem _root_.solution {z : ℂ} {k : ℤ} (hk : Odd k)
    (h : z.im = (k : ℝ) * Real.pi) :
    (Complex.exp z).im = 0 ∧ (Complex.exp z).re < 0 := by
  obtain ⟨m, hm⟩ := hk
  have hcast : (k : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) + Real.pi := by
    rw [hm]; push_cast; ring
  constructor
  · rw [Complex.exp_im, h, Real.sin_int_mul_pi, mul_zero]
  · rw [Complex.exp_re, h, hcast, Real.cos_int_mul_two_pi_add_pi]
    nlinarith [Real.exp_pos z.re]
end ExponentialJuliaSetMisiurewicz
