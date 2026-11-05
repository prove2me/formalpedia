-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ae_localised_diffuse_and_ordered_rightjump_H_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:31:07.564855+00:00
-- url     : https://prove2.me/submissions/20fc00d1-2ff1-4a20-911f-73617ebdc430

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (A : Ω → Set ℝ) (t : Ω → ι → ℝ≥0) (T : Ω → ℝ≥0)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ᵐ ω ∂P, MeasurableSet (A ω))
    (hregion : ∀ᵐ ω ∂P, ∀ s ∈ A ω,
      0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hInt : ∀ᵐ ω ∂P, IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (A ω) (dividendMeasure D ω))
    (hT : ∀ᵐ ω ∂P, ∀ i, t ω i ≤ T ω)
    (hPre : ∀ᵐ ω ∂P, ∀ i, t ω i = 0 ∨
      (t ω i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ᵐ ω ∂P, ∀ i,
      (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ᵐ ω ∂P, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (hLocalSecant : ∀ᵐ ω ∂P, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
      w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
        K * (rightLimit D (t ω i) ω - D (t ω i) ω)) :
    ∀ᵐ ω ∂P,
      (∫ s in A ω, Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
        ∂(dividendMeasure D ω)) +
      (∑' i : ι, Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) ≤ 0 := by
  filter_upwards [hA, hregion, hInt, hT, hPre, hPay, hInj,
    hLocalSecant] with ω ha hr hi ht hp hpay hinj hsec
  exact (avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
    X x D hD q hq w C hw_grad ω (A ω) ha hr hi
    hjump (t ω) (T ω) ht hp hpay hinj K hK hsec).1
