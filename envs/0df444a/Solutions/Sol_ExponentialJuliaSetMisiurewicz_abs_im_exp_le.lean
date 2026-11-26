-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.abs_im_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:27.828111+00:00
-- url     : https://prove2.me/submissions/54186b01-f055-4250-9fd5-723101bce34a

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution (w : ℂ) :
    |(Complex.exp w).im| ≤
      |w.im| * ‖Complex.exp w‖ := by
  rw [Complex.exp_im, Complex.norm_exp]
  rw [abs_mul, abs_of_pos (Real.exp_pos w.re)]
  have hsin : |Real.sin w.im| ≤ |w.im| := by
    exact Real.abs_sin_le_abs
  nlinarith [Real.exp_pos w.re, hsin]
end ExponentialJuliaSetMisiurewicz
