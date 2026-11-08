-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_natural_clock_integral_limit_closed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:58:32.136764+00:00
-- url     : https://prove2.me/submissions/5ce8bf61-a2ff-45e0-bba6-e1d7a52d3ef8

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_expectation_DCT

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-exact natural bounded-clock expectation convergence, including terminal cash atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFmeas : ∀ k, AEStronglyMeasurable (F k) P)
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hσeq : ∀ k ω, σ k ω = min (τ ω) (k : ℝ≥0)) :
    Tendsto (fun k => ∫ ω, F k ω ∂P) Filter.atTop
      (𝓝 (∫ ω, Term ω + Cash ω ∂P)) := by
  classical
  have hEvent : ∀ ω, ∀ᶠ k : ℕ in Filter.atTop,
      F k ω = Term ω + Cash ω :=
    avram_ubv_finite9_original_time_truncation_eventually_exact_closed_cash
      X x q C w D τ n hBound hτstop W Cash Term
      hW hCash hTerm σ hσeq F hFsource
  have hConv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => F k ω) Filter.atTop
        (𝓝 (Term ω + Cash ω)) := by
    filter_upwards [] with ω
    have hEq : (fun _ : ℕ => Term ω + Cash ω) =ᶠ[Filter.atTop]
        (fun k => F k ω) := by
      filter_upwards [hEvent ω] with k hk
      exact hk.symm
    exact tendsto_const_nhds.congr' hEq
  exact avram_ubv_finite9_original_F_family_expectation_DCT
    X x q hq C hfinite hxc w hw_cont hw_neg D hD
    τ hCashτI σ hσle F hFsource (fun ω => Term ω + Cash ω)
    hFmeas hConv
