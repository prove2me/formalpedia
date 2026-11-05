-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:36:44.18604+00:00
-- url     : https://prove2.me/submissions/b1866159-9e1c-43a1-980e-dff1f4d3e05b

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

/-- Original strict-horizon discounted cash is finite and continuous from below
    along a real cofinal family, including an arbitrary nonnegative real horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by
  have hfiniteS :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio ((⟨T, hT⟩ : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
    lt_of_le_of_lt
      (avram_p3_bv_original_strict_cash_rightlimit_bound
        D hD.1.1 ω (ruinTime X x D ω) ⟨T, hT⟩ q hq)
      ENNReal.ofReal_lt_top
  have hcoe : ((⟨T, hT⟩ : ℝ≥0) : ℝ) = T := rfl
  rw [hcoe] at hfiniteS
  exact avram_p3_bv_original_strict_cash_cofinal_real_iSup
    X x q T D ω u hmono hbelow hcover hfiniteS
