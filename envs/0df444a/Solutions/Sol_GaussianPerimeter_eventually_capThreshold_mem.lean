-- Prove2me | solution 1 for GaussianPerimeter.eventually_capThreshold_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:25:22.189786+00:00
-- url     : https://prove2.me/submissions/6ab032ca-9a13-4443-833d-ec7df7d3dcb2

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capRho_pos

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, capThreshold a n w ∈ Ioc (0 : ℝ) 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hρ := capRho_pos ha (show 0 < n by omega)
  have hrad : capRho a n ≤ capRadius a n w := by
    calc
      capRho a n = Real.sqrt (capRho a n ^ 2) := (Real.sqrt_sq hρ.le).symm
      _ ≤ capRadius a n w := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  exact ⟨div_pos hρ (hρ.trans_le hrad), (div_le_one (hρ.trans_le hrad)).2 hrad⟩
end GaussianPerimeter
