-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_C2_interior_random_clock_signed_atoms_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:52:02.470895+00:00
-- url     : https://prove2.me/submissions/3dc47c75-85a7-4ab3-b6cb-9fdd3d7429a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_countable_measurable_terms_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Compact interior C² localisation gives actual random-clock right-atom L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (s : ℝ≥0), (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (hPre : ∀ ω i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω i, x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    Integrable (fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P ∧
    (∀ᵐ ω ∂P, (∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) ≤ 0) := by
  have hBound : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          max 1 (K : ℝ) * (rightLimit D (t ω i) ω - D (t ω i) ω) := by
    intro ω i
    exact avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
      X x D hD C w hwC2 a b hOpen hBand K hK ω (t ω i)
      (hPre ω i) (hPost ω i)
  exact avram_p4_d_dividend_original_random_clock_countable_measurable_terms_L1
    X x q hq D hD w hjump t τ hT hPay hInj
    (max 1 (K : ℝ)) (le_max_left _ _) hBound
    Cash hCash hCashI hAtomTermMeas
