-- Prove2me | solution 1 for GaussianPerimeter.eventually_capMajorant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:24:45.366404+00:00
-- url     : https://prove2.me/submissions/5e5857a3-5248-40da-9fd1-e73cf71a3c78

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

theorem solution (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, 0 ≤ capMajorant a n w := by
  refine Filter.Eventually.of_forall (fun n => ?_)
  have hρ : 0 ≤ capRho a n := by unfold capRho; positivity
  have hR0 : 0 ≤ capRadius a n w := by unfold capRadius; positivity
  have hR : capRho a n ≤ capRadius a n w := by
    unfold capRadius
    calc capRho a n = Real.sqrt (capRho a n ^ 2) := (Real.sqrt_sq hρ).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) - 1) + w)])
  have ht0 : 0 ≤ capThreshold a n w := by unfold capThreshold; exact div_nonneg hρ hR0
  have ht1 : capThreshold a n w ≤ 1 := by
    unfold capThreshold
    rcases hR0.eq_or_lt with h | h
    · rw [← h, div_zero]; norm_num
    · exact (div_le_one h).2 hR
  have hN : 0 ≤ capNormalizer n := by
    unfold capNormalizer
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    unfold capProfile
    apply Real.rpow_nonneg
    nlinarith [hu.1, hu.2]
  unfold capMajorant
  dsimp only
  apply div_nonneg
  · apply Real.rpow_nonneg
    nlinarith
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ht0) hN
