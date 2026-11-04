-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_postpayment_cash_terminal_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:52:09.086044+00:00
-- url     : https://prove2.me/submissions/fda956b8-fe20-459f-9ecb-e3533f32d8ff

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped cash and post-right-payment reserve have a
nonpositive cap-linear dividend remainder on the zero-or-pre-ruin branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    Cash ω + (V (W ω) - V (x + X.X (τ ω) ω)) ≤ 0 := by
  have hDomain :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
        Icc (0 : ℝ) (τ ω : ℝ) :=
    avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
      X x D ω τ hPre
  have hBound :=
    avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
      X x C q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω (τ ω) hPre
  calc
    Cash ω + (V (W ω) - V (x + X.X (τ ω) ω)) =
        (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal +
          (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
            V (x + X.X (τ ω) ω)) := by
              rw [hCash ω, hDomain, hW ω, if_pos hPre]
    _ ≤ 0 := hBound