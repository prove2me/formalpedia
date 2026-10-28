-- Prove2me | solution 1 for AvramDividend.Classical.finite_negative_jump_exp_integral_tendsto_zero_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:08:25.858789+00:00
-- url     : https://prove2.me/submissions/c9795ab0-ef56-4900-9e15-4317b46543ed

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology

theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν)
      atTop (𝓝 0) := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ] using hFinite
  have hmem : ∀ᵐ y : ℝ ∂μ, y < 0 := by
    exact ae_restrict_mem measurableSet_Iio
  have hMeas (n : ℕ) :
      AEStronglyMeasurable
        (fun y : ℝ => Real.exp ((n : ℝ) * y)) μ := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hBound (n : ℕ) :
      ∀ᵐ y : ℝ ∂μ,
        ‖Real.exp ((n : ℝ) * y)‖ ≤ (1 : ℝ) := by
    filter_upwards [hmem] with y hy
    have hy0 : (n : ℝ) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hy)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_one_iff).2 hy0
  have hPoint :
      ∀ᵐ y : ℝ ∂μ,
        Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * y)) atTop (𝓝 0) := by
    filter_upwards [hmem] with y hy
    have hmul :
        Tendsto (fun n : ℕ => (n : ℝ) * y) atTop atBot :=
      Filter.Tendsto.atTop_mul_const_of_neg hy
        tendsto_natCast_atTop_atTop
    exact Real.tendsto_exp_atBot.comp hmul
  have hDCT :=
    tendsto_integral_of_dominated_convergence
      (μ := μ) (F := fun n y => Real.exp ((n : ℝ) * y))
      (f := fun _ : ℝ => (0 : ℝ))
      (fun _ : ℝ => (1 : ℝ))
      hMeas (integrable_const _) hBound hPoint
  simpa [μ] using hDCT
