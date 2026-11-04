-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ubv_interior_band_absolute_rightjump_le_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:44:00.921917+00:00
-- url     : https://prove2.me/submissions/5304aa60-ea5f-4ae8-82d2-831f74ab64a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- C² inside the actual source reserve band controls total original rightjump cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hStates : ∀ i, riskProcess X x D (t i) ω ∈ Icc a b ∧
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (max 1 (K : ℝ) - 1) *
          (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal) := by
  have hLip := avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
    C w hwC2 a b hOpen hBand K hK
  have hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          max 1 (K : ℝ) *
            (rightLimit D (t i) ω - D (t i) ω) := by
    intro i
    have hPayNonneg : 0 ≤ rightLimit D (t i) ω - D (t i) ω :=
      sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω (t i))
    have hChron :
        riskProcess X x D (t i) ω -
          (x + X.X (t i) ω - rightLimit D (t i) ω) =
            rightLimit D (t i) ω - D (t i) ω := by
      simp only [riskProcess]
      ring
    calc
      w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        |w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω)| := le_abs_self _
      _ ≤ (K : ℝ) *
          |riskProcess X x D (t i) ω -
            (x + X.X (t i) ω - rightLimit D (t i) ω)| :=
        hLip _ (hStates i).1 _ (hStates i).2
      _ = (K : ℝ) * (rightLimit D (t i) ω - D (t i) ω) := by
        rw [hChron, abs_of_nonneg hPayNonneg]
      _ ≤ max 1 (K : ℝ) * (rightLimit D (t i) ω - D (t i) ω) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (K : ℝ)) hPayNonneg
  exact avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
    X x q hq D hD w hjump t ω T hT hPre hPay
    (max 1 (K : ℝ)) (le_max_left 1 (K : ℝ)) hLocalSecant
