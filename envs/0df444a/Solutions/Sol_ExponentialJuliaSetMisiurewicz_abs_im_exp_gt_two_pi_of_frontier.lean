-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.abs_im_exp_gt_two_pi_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:40.111203+00:00
-- url     : https://prove2.me/submissions/65c07bfe-4a30-43b8-a84f-957e8dd70251

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
theorem _root_.solution
    {z : ℂ} (hfr : |z.im| = Real.pi / 3) (hre : 4 < z.re) :
    2 * Real.pi < |(Complex.exp z).im| := by
  have hsin : |Real.sin z.im| = Real.sqrt 3 / 2 := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ Real.pi / 3) |>.mp hfr with h | h
    · rw [h, abs_of_pos (by rw [Real.sin_pi_div_three]; positivity),
        Real.sin_pi_div_three]
    · rw [h, Real.sin_neg, abs_neg,
        abs_of_pos (by rw [Real.sin_pi_div_three]; positivity),
        Real.sin_pi_div_three]
  have hexp : Real.exp 4 ≤ Real.exp z.re := Real.exp_le_exp.mpr (le_of_lt hre)
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hsq : (4 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [h1]
    have hid : Real.exp 1 ^ 4 = (Real.exp 1 ^ 2) ^ 2 := by ring
    rw [h4, hid]
    nlinarith [hsq]
  have hsqrt : (1.7 : ℝ) < Real.sqrt 3 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hpi : Real.pi < 4 := Real.pi_lt_four
  rw [Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _), hsin]
  nlinarith [Real.exp_pos z.re, Real.sqrt_nonneg 3]
end ExponentialJuliaSetMisiurewicz
