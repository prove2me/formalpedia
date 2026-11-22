-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_random_ruinclock_cofinal_prepayment_cash_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:11:30.088661+00:00
-- url     : https://prove2.me/submissions/4f6778d0-f909-4216-aca6-9eafb9eedcd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_cofinal_strict_reward_left_limit
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q)
    (ρ : Ω → ℝ≥0)
    (hρpos : ∀ ω, 0 < ρ ω)
    (hρle : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → Ω → ℝ≥0)
    (hMono : ∀ ω, Monotone (fun j => u j ω))
    (hStrict : ∀ j ω, u j ω < ρ ω)
    (hLimit : ∀ ω,
      Tendsto (fun j => u j ω) atTop (𝓝[<] (ρ ω))) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun j =>
          Real.exp (-(q * (u j ω : ℝ))) *
            w (x + X.X (u j ω) ω - rightLimit D (u j ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (u j ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)
        atTop
        (𝓝 (Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)) := by
  classical
  have hP : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      ∀ (v : ℕ → ℝ≥0), Monotone v →
        (∀ j, v j < t) → Tendsto v atTop (𝓝[<] t) →
        Tendsto
          (fun j =>
            Real.exp (-(q * (v j : ℝ))) *
              w (x + X.X (v j) ω - rightLimit D (v j) ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (v j : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)
          atTop
          (𝓝 (Real.exp (-(q * (t : ℝ))) *
              w (riskProcess X x D t ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (t : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)) :=
    avram_gclose17_original_cofinal_strict_reward_left_limit
      X hν x C D hD w hw q hq
  filter_upwards [hP] with ω hω
  exact hω (ρ ω) (hρpos ω) (hρle ω)
    (fun j => u j ω) (hMono ω)
    (fun j => hStrict j ω) (hLimit ω)
