-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:27:37.13239+00:00
-- url     : https://prove2.me/submissions/c547772c-95a0-479a-8e86-7f56955fae0c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The true stopped dividend cash envelope gives an integrable nonpositive correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash Hdiv : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hHmeas : AEStronglyMeasurable Hdiv P)
    (K : ℝ) (hK : 1 ≤ K)
    (hHsign : ∀ᵐ ω ∂P, Hdiv ω ≤ 0)
    (hHupper : ∀ᵐ ω ∂P, -Hdiv ω ≤ (K - 1) * Cash ω) :
    Integrable Hdiv P ∧ (∀ᵐ ω ∂P, Hdiv ω ≤ 0) := by
  have hCashNN : ∀ ω, 0 ≤ Cash ω := by
    intro ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hKNN : 0 ≤ K - 1 := sub_nonneg.mpr hK
  have hScaled : Integrable (fun ω => (K - 1) * Cash ω) P :=
    hCashI.const_mul (K - 1)
  have hNorm : ∀ᵐ ω ∂P, ‖Hdiv ω‖ ≤ ‖(K - 1) * Cash ω‖ := by
    filter_upwards [hHsign, hHupper] with ω hs hu
    have hProd : 0 ≤ (K - 1) * Cash ω := mul_nonneg hKNN (hCashNN ω)
    simpa only [Real.norm_eq_abs, abs_of_nonpos hs, abs_of_nonneg hProd] using hu
  exact ⟨hScaled.mono hHmeas hNorm, hHsign⟩
