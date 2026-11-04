-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:06:17.123428+00:00
-- url     : https://prove2.me/submissions/c9631d3d-e525-4734-8115-3a882036aa75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_payment_window_closed_horizon_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Closed source dividend atoms and diffuse cash equal P4-F's actual stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) :
    (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
        ∂((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let A : Set ℝ := paymentTimes σ
  let B : Set ℝ := Icc (0 : ℝ) (T : ℝ)
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  have hA : MeasurableSet A :=
    avram_p4_d_dividend_original_paymentTimes_measurableSet σ
  have hWindow : A ∩ Iic (T : ℝ) = A ∩ B :=
    avram_p4_d_dividend_original_payment_window_closed_horizon_exact σ T
  change (∫⁻ s : ℝ, (if s ∈ A then f s else 0) ∂(μ.restrict B)) =
    (∫⁻ s in A ∩ Iic (T : ℝ), f s ∂μ)
  calc
    _ = ∫⁻ s : ℝ, A.indicator f s ∂(μ.restrict B) := by
      congr 1
    _ = ∫⁻ s in A, f s ∂(μ.restrict B) := lintegral_indicator hA f
    _ = ∫⁻ s in A ∩ B, f s ∂μ := by
      exact congrArg (fun ν : Measure ℝ => ∫⁻ s : ℝ, f s ∂ν)
        (Measure.restrict_restrict hA)
    _ = ∫⁻ s in A ∩ Iic (T : ℝ), f s ∂μ := by
      rw [hWindow]
