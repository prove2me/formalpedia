-- Prove2me | solution 1 for GaussianPerimeter.radialKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:28.679471+00:00
-- url     : https://prove2.me/submissions/b9a9b297-350f-42f8-9506-72cd90795e44

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
theorem _root_.solution (n : ℕ) : Integrable (radialKernel n) := by
  unfold radialKernel
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  refine (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (s := ((n - 1 : ℕ) : ℝ))
    (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (n - 1)])).congr_fun (fun r _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast]
  congr 2
  ring
end GaussianPerimeter
