-- Prove2me | solution 2 for GaussianPerimeter.eventually_capMajorant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:57.227526+00:00
-- url     : https://prove2.me/submissions/8956c9e7-7634-4fe0-8058-03cf5f24a361

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_eventually_capThreshold_mem
section
@[expose] public section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace GaussianPerimeter
private theorem capProfile_nonneg {n : ℕ} {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ capProfile n x := by
  have h := sq_le_sq' hx.1 hx.2
  exact Real.rpow_nonneg (by linarith) _
private theorem capNormalizer_nonneg (n : ℕ) : 0 ≤ capNormalizer n := by
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ hx => capProfile_nonneg hx
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, 0 ≤ capMajorant a n w := by
  filter_upwards [eventually_capThreshold_mem a w ha] with n ht
  have hsq := sq_le_sq' (show -(1 : ℝ) ≤ capThreshold a n w by linarith [ht.1]) ht.2
  have hb : 0 ≤ 1 - capThreshold a n w ^ 2 := by linarith
  unfold capMajorant
  exact div_nonneg (Real.rpow_nonneg hb _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1.le) (capNormalizer_nonneg _))
end GaussianPerimeter
