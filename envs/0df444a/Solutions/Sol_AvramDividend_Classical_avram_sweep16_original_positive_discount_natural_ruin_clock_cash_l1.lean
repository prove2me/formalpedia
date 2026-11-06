-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_positive_discount_natural_ruin_clock_cash_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:17:40.920745+00:00
-- url     : https://prove2.me/submissions/c32454a1-b13e-4b48-8fba-27c5cda4564e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  obtain ⟨θ, hθ, hψ⟩ :=
    avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount X q hq
  exact avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
    X x C D hD θ hθ q (le_of_lt hψ) τ hτmeas
