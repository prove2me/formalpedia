-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_zero_horizon_full_stieltjes_mass_even_immediate_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:52.753426+00:00
-- url     : https://prove2.me/submissions/c21fead0-1338-4c5d-91d6-9faa0659df7d

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

/-- Even at immediate ruin, the original zero-horizon stopped dividend measure includes the full time-zero rightpayment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ)) =
        ENNReal.ofReal (rightLimit D 0 ω) := by
  have hset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) =
        Icc (0 : ℝ) (0 : ℝ) := by
    ext t
    change ((0 ≤ t ∧
      (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω)) ∧
        t ≤ 0) ↔ (0 ≤ t ∧ t ≤ 0)
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      have htzero : t = 0 := le_antisymm ht.2 ht.1
      exact ⟨⟨ht.1, Or.inl htzero⟩, ht.2⟩
  rw [hset]
  exact avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
    D hD ω 0
