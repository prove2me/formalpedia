-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:48:43.566659+00:00
-- url     : https://prove2.me/submissions/6a398a68-462e-4c8e-a6c2-b46a7903cc93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Every original Stieltjes payout before a strictly surviving horizon,
    including the zero and horizon rightpayment atoms and all diffuse mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) =
        ENNReal.ofReal (rightLimit D T ω) := by
  have hset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) =
        Icc 0 (T : ℝ) := by
    ext t
    change ((0 ≤ t ∧
      (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω)) ∧
        t ≤ (T : ℝ)) ↔ (0 ≤ t ∧ t ≤ (T : ℝ))
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      have hle : ENNReal.ofReal t ≤ (T : ℝ≥0∞) := by
        calc
          ENNReal.ofReal t ≤ ENNReal.ofReal (T : ℝ) :=
            ENNReal.ofReal_le_ofReal ht.2
          _ = (T : ℝ≥0∞) := by simp
      exact ⟨⟨ht.1, Or.inr (lt_of_le_of_lt hle hstrict)⟩, ht.2⟩
  rw [hset]
  exact avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
