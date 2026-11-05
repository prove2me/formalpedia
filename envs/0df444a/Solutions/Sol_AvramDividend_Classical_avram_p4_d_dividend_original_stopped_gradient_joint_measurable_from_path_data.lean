-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:05:33.193277+00:00
-- url     : https://prove2.me/submissions/17bb479c-1b5c-4d1a-bc3e-5dd70eb0f59a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint measurability of the original left-source, right-dividend,
derivative and stopped-window data yields a jointly strongly measurable
discounted dividend-gradient integrand in its exact source convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (hXL : Measurable (fun p : Ω × ℝ =>
      Function.leftLim (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal))
    (hDR : Measurable (fun p : Ω × ℝ =>
      rightLimit D p.2.toNNReal p.1))
    (hDeriv : Measurable (deriv w))
    (hWindow : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2) := by
  have hReserve : Measurable (fun p : Ω × ℝ =>
      x + Function.leftLim (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal -
        rightLimit D p.2.toNNReal p.1) :=
    (measurable_const.add hXL).sub hDR
  have hGradient : Measurable (fun p : Ω × ℝ =>
      1 - deriv w (x + Function.leftLim
        (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal -
        rightLimit D p.2.toNNReal p.1)) :=
    measurable_const.sub (hDeriv.comp hReserve)
  have hDiscount : Measurable (fun p : Ω × ℝ =>
      Real.exp (-(q * p.2))) := by fun_prop
  have hIntegrand : Measurable (fun p : Ω × ℝ =>
      Real.exp (-(q * p.2)) *
        (1 - deriv w (x + Function.leftLim
          (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal -
          rightLimit D p.2.toNNReal p.1))) :=
    hDiscount.mul hGradient
  have hIndicator := hIntegrand.indicator hWindow
  exact hIndicator.stronglyMeasurable
