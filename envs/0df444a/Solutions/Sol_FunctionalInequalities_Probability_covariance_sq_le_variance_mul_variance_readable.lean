-- Prove2me | solution 1 for FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:45.961502+00:00
-- url     : https://prove2.me/submissions/0306b1e4-1955-40d2-bfc3-148334a1798d

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_CauchySchwarz

noncomputable section
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
/-- **Covariance Cauchy–Schwarz**: `cov[X, Y]² ≤ Var X · Var Y` for `X, Y ∈ L²`. -/
theorem solution {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
    have hpoly (t : ℝ) :
        0 ≤ variance X μ * t ^ 2 - 2 * covariance X Y μ * t + variance Y μ := by
      let Z : Ω → ℝ := fun ω => Y ω - t * X ω
      have hXt : MemLp (fun ω => t * X ω) 2 μ := hX.const_mul t
      have hZ : MemLp Z 2 μ := hY.sub hXt
      have hnonneg : 0 ≤ variance Z μ := variance_nonneg Z μ
      rw [← covariance_self hZ.aestronglyMeasurable.aemeasurable] at hnonneg
      change 0 ≤
        covariance (fun ω => Y ω - t * X ω)
          (fun ω => Y ω - t * X ω) μ at hnonneg
      rw [covariance_fun_sub_left hY hXt hZ,
        covariance_fun_sub_right hY hY hXt,
        covariance_const_mul_left t,
        covariance_const_mul_right t] at hnonneg
      rw [covariance_fun_sub_right hX hY hXt,
        covariance_const_mul_right t,
        covariance_self hY.aestronglyMeasurable.aemeasurable,
        covariance_self hX.aestronglyMeasurable.aemeasurable] at hnonneg
      have hcomm : covariance Y X μ = covariance X Y μ := by
        rw [covariance_comm]
      rw [hcomm] at hnonneg
      nlinarith

    have hVX : 0 ≤ variance X μ := variance_nonneg X μ
    have hVY : 0 ≤ variance Y μ := variance_nonneg Y μ
    by_cases hzero : variance X μ = 0
    · have hcov : covariance X Y μ = 0 := by
        by_contra hc
        let t : ℝ := (variance Y μ + 1) / (2 * covariance X Y μ)
        have ht := hpoly t
        have hden : 2 * covariance X Y μ ≠ 0 := by
          intro h
          apply hc
          nlinarith
        have hcalc :
            2 * covariance X Y μ * t = variance Y μ + 1 := by
          dsimp [t]
          field_simp
        nlinarith
      simp [hzero, hcov]
    · have hpos : 0 < variance X μ := lt_of_le_of_ne hVX (Ne.symm hzero)
      let t : ℝ := covariance X Y μ / variance X μ
      have ht := hpoly t
      have hcalc : variance X μ * t = covariance X Y μ := by
        dsimp [t]
        field_simp
      nlinarith
