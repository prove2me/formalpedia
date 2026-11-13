-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_contact_stieltjes_restrict_eq_drift_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:17:03.739045+00:00
-- url     : https://prove2.me/submissions/3f2ce407-f5bc-411d-bdde-f4dbe258ace9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) (hd : 0 ≤ X.drift)
    (hCashFinite : dividendMeasure D ω (Ioc (0 : ℝ) T) < ⊤)
    (hZero : ∀ t : ℝ≥0, (t : ℝ) ≤ T → riskProcess X x D t ω = 0)
    (hActive : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hLine : ∀ a b : ℝ≥0, a ≤ b → (b : ℝ) ≤ T →
      X.X b ω - X.X a ω = X.drift * ((b : ℝ) - (a : ℝ))) :
    (dividendMeasure D ω).restrict (Ioc 0 T) =
      (ENNReal.ofReal X.drift • (volume : Measure ℝ)).restrict (Ioc 0 T) := by
  apply measure_restrict_Ioc_eq_of_local_Ioc_agreement
    (dividendMeasure D ω) (ENNReal.ofReal X.drift • (volume : Measure ℝ))
    T hT hCashFinite
  intro s t hs hst ht
  let a : ℝ≥0 := ⟨s, hs⟩
  let b : ℝ≥0 := ⟨t, le_trans hs hst⟩
  have hab : a ≤ b := hst
  have hta : (a : ℝ) ≤ T := le_trans hst ht
  have htb : (b : ℝ) ≤ T := ht
  have hcell :=
    avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
      X hBV hFinite x C D hD ω a b hab
      (hActive a hta) (hActive b htb)
      (hZero a hta) (hZero b htb) (hLine a b hab htb)
  change (dividendMeasure D ω) (Ioc s t) =
    ENNReal.ofReal (X.drift * (t - s)) at hcell
  calc
    (dividendMeasure D ω) (Ioc s t) =
        ENNReal.ofReal (X.drift * (t - s)) := hcell
    _ = ENNReal.ofReal X.drift * ENNReal.ofReal (t - s) := by
      rw [ENNReal.ofReal_mul hd]
    _ = (ENNReal.ofReal X.drift • (volume : Measure ℝ)) (Ioc s t) := by
      simp [Measure.smul_apply, Real.volume_Ioc]
