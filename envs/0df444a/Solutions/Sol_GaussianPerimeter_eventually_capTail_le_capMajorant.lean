-- Prove2me | solution 1 for GaussianPerimeter.eventually_capTail_le_capMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:07.839474+00:00
-- url     : https://prove2.me/submissions/33a2d645-a17a-4dfa-89fd-33ef63361184

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capTail_le
public import Theorems.Thm_GaussianPerimeter_eventually_capThreshold_mem

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, capTail n (capThreshold a n w) ≤ capMajorant a n w := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_capThreshold_mem a w ha] with n hn ht
  exact capTail_le hn ht.1 ht.2
end GaussianPerimeter
