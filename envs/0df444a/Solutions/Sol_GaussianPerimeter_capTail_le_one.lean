-- Prove2me | solution 1 for GaussianPerimeter.capTail_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:46.881795+00:00
-- url     : https://prove2.me/submissions/650e4bb1-0f15-43bf-b63c-b3253563c20f

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capProfile_continuous
public import Theorems.Thm_GaussianPerimeter_capNormalizer_pos
section
@[expose] public section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace GaussianPerimeter
private theorem capProfile_nonneg {n : ℕ} {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ capProfile n x := by
  have h := sq_le_sq' hx.1 hx.2
  exact Real.rpow_nonneg (by linarith) _
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
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    capTail n t ≤ 1 := by
  rw [capTail, div_le_one (capNormalizer_pos hn)]
  exact intervalIntegral.integral_mono_interval (by linarith [ht.1]) ht.2 le_rfl
    ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun x hx => capProfile_nonneg (Ioc_subset_Icc_self hx)))
    ((capProfile_continuous hn).intervalIntegrable _ _)
end GaussianPerimeter
