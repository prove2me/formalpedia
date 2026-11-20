-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_ruinclipped_finite_barrier_Hsource_zero_at_exact_negative_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:36:51.184638+00:00
-- url     : https://prove2.me/submissions/3bf01c4e-16e3-4d41-9684-05f9560331e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a q : ℝ) (w : ℝ → ℝ)
    (hNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (ω : Ω) (σ : ℝ≥0) (hPos : 0 < σ)
    (hExact : (σ : ℝ≥0∞) =
      ruinTime X x (barrierStrategy X x a) ω)
    (hRuin : riskProcess X x (barrierStrategy X x a) σ ω < 0)
    (hCash :
      (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω)
          ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0)
    (H : ℝ)
    (hSource : H =
      Real.exp (-(q * (σ : ℝ))) *
        w (if σ = 0 ∨
              (σ : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω then
          x + X.X σ ω - rightLimit (barrierStrategy X x a) σ ω
        else riskProcess X x (barrierStrategy X x a) σ ω) +
      (∫⁻ s in paymentTimes (ruinTime X x (barrierStrategy X x a) ω)
          ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure (barrierStrategy X x a) ω)).toReal) :
    H = 0 := by
  have hnot : ¬ (σ = 0 ∨
      (σ : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω) := by
    push_neg
    constructor
    · exact ne_of_gt hPos
    · rw [← hExact]
  rw [hSource]
  simp [hnot, hNeg _ hRuin, hCash]
