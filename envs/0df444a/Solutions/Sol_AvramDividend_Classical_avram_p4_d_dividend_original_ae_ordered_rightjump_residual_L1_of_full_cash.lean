-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ae_ordered_rightjump_residual_L1_of_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:48:27.31223+00:00
-- url     : https://prove2.me/submissions/d264ea9a-94f9-4988-9e5b-7fa7a687361e

import Mathlib.Probability.Process.Filtration
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
        K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash Atom : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hAtom : ∀ ω, Atom ω = (∑' i : ι, Real.exp (-(q * (t ω i : ℝ))) *
          ((rightLimit D (t ω i) ω - D (t ω i) ω) +
            w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
            w (riskProcess X x D (t ω i) ω))))
    (hCashI : Integrable Cash P)
    (hAtomMeas : AEStronglyMeasurable Atom P) :
    Integrable Atom P := by
  have hDominating : Integrable (fun ω => (K - 1) * Cash ω) P :=
    hCashI.const_mul (K - 1)
  apply hDominating.mono' hAtomMeas
  filter_upwards [hA, hregion, hInt, hT, hPre, hPay, hInj,
    hLocalSecant] with ω ha hr hi ht hp hpay hinj hsec
  obtain ⟨_, _, hAbs, hBound⟩ :=
    avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
      X x D hD q hq w C hw_grad ω (A ω) ha hr hi
      hjump (t ω) (T ω) ht hp hpay hinj K hK hsec
  have hSum : |Atom ω| ≤ (∑' i : ι, |Real.exp (-(q * (t ω i : ℝ))) *
          ((rightLimit D (t ω i) ω - D (t ω i) ω) +
            w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
            w (riskProcess X x D (t ω i) ω))|) := by
    rw [hAtom ω]
    have hNorm : Summable (fun i : ι =>
      ‖Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))‖) := by
      simpa only [Real.norm_eq_abs] using hAbs
    simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm hNorm)
  calc
    ‖Atom ω‖ = |Atom ω| := Real.norm_eq_abs _
    _ ≤ _ := hSum
    _ ≤ (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := hBound
    _ = (K - 1) * Cash ω := by rw [hCash ω]
