-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:05:30.810572+00:00
-- url     : https://prove2.me/submissions/5a3d2784-72f1-4361-840d-3c86c138cf89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hpostzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpostzerob : riskProcess X x D b ω -
      (rightLimit D b ω - D b ω) = 0)
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by
  have hstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hinc : rightLimit D b ω - rightLimit D a ω =
      X.X b ω - X.X a ω := by
    unfold riskProcess at hpostzeroa hpostzerob
    linarith
  rw [dividendMeasure_Ioc_rightLimit D hstrat ω a b, hinc, hline]
