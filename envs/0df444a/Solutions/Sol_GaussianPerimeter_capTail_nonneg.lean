-- Prove2me | solution 1 for GaussianPerimeter.capTail_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:42.416601+00:00
-- url     : https://prove2.me/submissions/afa9f5a1-35e0-4ee9-8cb5-b92331c96a3f

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
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
theorem _root_.solution {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ capTail n t := by
  apply div_nonneg _ (capNormalizer_nonneg n)
  exact intervalIntegral.integral_nonneg ht.2 fun x hx =>
    capProfile_nonneg ⟨(by linarith [ht.1] : (-1 : ℝ) ≤ t).trans hx.1, hx.2⟩
end GaussianPerimeter
