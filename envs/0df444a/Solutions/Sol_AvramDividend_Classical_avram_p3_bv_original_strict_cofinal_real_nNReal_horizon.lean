-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:24:29.998682+00:00
-- url     : https://prove2.me/submissions/f1b1881d-f96d-4c9f-940c-42137fcc40e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_real_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine NNReal stopping horizon lets the strict real Stieltjes cash
converge cofinally without extra pathwise finiteness assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by
  have hfinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
    lt_of_le_of_lt
      (avram_p3_bv_original_strict_cash_rightlimit_bound
        D hD.1.1 ω (ruinTime X x D ω) S q hq)
      ENNReal.ofReal_lt_top
  exact avram_p3_bv_original_strict_cash_cofinal_real_iSup
    X x q (S : ℝ) D ω u hmono hbelow hcover hfinite
