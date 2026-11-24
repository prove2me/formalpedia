-- Prove2me | solution 1 for GaussianPerimeter.capProfile_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:08:33.086696+00:00
-- url     : https://prove2.me/submissions/6ad35392-e4cb-4f17-b85b-6c01f4379e2b

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : Continuous (capProfile n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact (continuous_const.sub (continuous_id.pow 2)).rpow_const
    (fun _ => Or.inr (by linarith))
end GaussianPerimeter
