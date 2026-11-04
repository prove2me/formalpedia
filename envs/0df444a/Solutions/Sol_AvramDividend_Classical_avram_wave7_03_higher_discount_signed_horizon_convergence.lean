-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_higher_discount_signed_horizon_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:46:40.901212+00:00
-- url     : https://prove2.me/submissions/de68f519-8833-4fda-a12a-8910a191fe3e

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original discounted dividend value gives almost-sure convergence of
    genuine signed Stieltjes cash horizons at every stronger discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hFinite : dividendValue X q₁ x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))) := by
  have hFinite₂ : dividendValue X q₂ x D < ⊤ :=
    lt_of_le_of_lt
      (avram_wave7_03_original_dividendValue_antitone_discount
        X x D q₁ q₂ hq) hFinite
  exact avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
    X x D hD q₂ hFinite₂
