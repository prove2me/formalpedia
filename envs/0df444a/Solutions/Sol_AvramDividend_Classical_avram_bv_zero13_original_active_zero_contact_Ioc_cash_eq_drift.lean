-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:35:38.322204+00:00
-- url     : https://prove2.me/submissions/86bbd08d-c75c-4da7-8bfe-e1305fa7cb91

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    (hactivea : a = 0 ∨ (a : ℝ≥0∞) < ruinTime X x D ω)
    (hactiveb : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω)
    (hzeroa : riskProcess X x D a ω = 0)
    (hzerob : riskProcess X x D b ω = 0)
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by
  have hstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have ha_le : D a ω ≤ rightLimit D a ω :=
    dividendStrategy_le_rightLimit D hstrat ω a
  have hb_le : D b ω ≤ rightLimit D b ω :=
    dividendStrategy_le_rightLimit D hstrat ω b
  have ha_cap : rightLimit D a ω - D a ω ≤ riskProcess X x D a ω :=
    hD.1.2 ω a hactivea
  have hb_cap : rightLimit D b ω - D b ω ≤ riskProcess X x D b ω :=
    hD.1.2 ω b hactiveb
  have ha_eq : rightLimit D a ω = D a ω := by
    rw [hzeroa] at ha_cap
    linarith
  have hb_eq : rightLimit D b ω = D b ω := by
    rw [hzerob] at hb_cap
    linarith
  have hinc : D b ω - D a ω =
      X.X b ω - X.X a ω := by
    unfold riskProcess at hzeroa hzerob
    linarith
  rw [dividendMeasure_Ioc_rightLimit D hstrat ω a b, hb_eq, ha_eq,
    hinc, hline]
