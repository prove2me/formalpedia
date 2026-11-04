-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_survival_horizon_atom_absorption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:46:35.28143+00:00
-- url     : https://prove2.me/submissions/c1f94cf8-bb5f-40c7-813e-2c5319ecbc40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On strict survival, the exact horizon payment atom is absorbed by
    the drop from the prepayment to the postpayment terminal value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hsplit := avram_p3_bv_real_cash_split_ae X x C D hD q T hT
  filter_upwards [hsplit] with ω hω
  intro hactive
  have hSval : (S : ℝ) = T := rfl
  have hset :
      (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ) =
        paymentTimes (ruinTime X x D ω) ∩ ({T} : Set ℝ) := by
    rw [hSval]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨ha, _⟩, ht⟩
      exact ⟨ha, ht⟩
    · rintro ⟨ha, ht⟩
      exact ⟨⟨ha, le_of_eq ht⟩, ht⟩
  have hpost : riskProcess X x D S ω -
      (rightLimit D S ω - D S ω) =
        x + X.X S ω - rightLimit D S ω := by
    change (x + X.X S ω - D S ω) -
      (rightLimit D S ω - D S ω) =
        x + X.X S ω - rightLimit D S ω
    ring
  have hatom :=
    avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
      X x D hD.1.1 w hjump ω S (Or.inr hactive) q
  have hatom' :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ ({T} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) ≤
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) := by
    rw [hSval] at hatom
    rw [hSval] at hset
    rw [hset] at hatom
    simpa only [hpost] using hatom
  rw [hω]
  linarith only [hatom']
