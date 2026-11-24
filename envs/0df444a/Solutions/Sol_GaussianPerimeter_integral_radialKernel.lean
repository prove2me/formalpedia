-- Prove2me | solution 1 for GaussianPerimeter.integral_radialKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:35:50.841119+00:00
-- url     : https://prove2.me/submissions/09155916-da6f-4cab-ac9c-572e880ba932

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ, radialKernel n r) =
      (1 / 2 : ℝ) ^ (-(n : ℝ) / 2) * (1 / 2) * Real.Gamma ((n : ℝ) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((n - 1 : ℕ) : ℝ))
    (b := 1 / 2) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (n - 1)]) (by norm_num)
  have hk : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hk] at h
  rw [radialKernel, integral_indicator measurableSet_Ioi, ← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [Real.rpow_natCast, Real.rpow_two]
  congr 2
  ring
end GaussianPerimeter
