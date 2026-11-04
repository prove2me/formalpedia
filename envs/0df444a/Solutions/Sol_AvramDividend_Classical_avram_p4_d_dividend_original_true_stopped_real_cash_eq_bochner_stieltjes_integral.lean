-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_real_cash_eq_bochner_stieltjes_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:37:03.210514+00:00
-- url     : https://prove2.me/submissions/bd287339-a23e-4441-8467-a3e1bde3df90

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real-valued original stopped Cash is exactly the source Stieltjes Bochner integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    ∫ s in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * s)) ∂(dividendMeasure D ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(q * u))) s μ :=
    avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
      D hD ω σ T q hq
  have hnonneg : 0 ≤ᵐ[μ.restrict s] (fun u : ℝ => Real.exp (-(q * u))) :=
    Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
  have hreal : 0 ≤ ∫ u in s, Real.exp (-(q * u)) ∂μ :=
    integral_nonneg_of_ae hnonneg
  have heq :
      ENNReal.ofReal (∫ u in s, Real.exp (-(q * u)) ∂μ) =
        ∫⁻ u in s, ENNReal.ofReal (Real.exp (-(q * u))) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  calc
    (∫⁻ u in s, ENNReal.ofReal (Real.exp (-(q * u))) ∂μ).toReal =
        (ENNReal.ofReal (∫ u in s, Real.exp (-(q * u)) ∂μ)).toReal :=
      congrArg ENNReal.toReal heq.symm
    _ = ∫ u in s, Real.exp (-(q * u)) ∂μ :=
      ENNReal.toReal_ofReal hreal
