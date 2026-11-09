-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:28:28.347234+00:00
-- url     : https://prove2.me/submissions/3131ef26-faa2-49b2-83f0-d3cd9c04921f

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

/-- Actual BV source-drift cash bound from a postpayment-zero restart. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpositiveb : 0 ≤ riskProcess X x D b ω -
      (rightLimit D b ω - D b ω))
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by
  have hstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hidentity :
      rightLimit D b ω - rightLimit D a ω =
        X.X b ω - X.X a ω -
          (riskProcess X x D b ω -
            (rightLimit D b ω - D b ω)) +
          (riskProcess X x D a ω -
            (rightLimit D a ω - D a ω)) := by
    unfold riskProcess
    ring
  have hcash : rightLimit D b ω - rightLimit D a ω ≤
      X.drift * ((b : ℝ) - (a : ℝ)) := by
    rw [hidentity, hline, hzeroa]
    linarith [hpositiveb]
  rw [dividendMeasure_Ioc_rightLimit D hstrat ω a b]
  exact ENNReal.ofReal_le_ofReal hcash
