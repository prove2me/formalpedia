-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:37:04.601213+00:00
-- url     : https://prove2.me/submissions/8b5cc1f9-ef71-4071-9728-8102a3337fdb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original real stopped cash retains exactly the physical right-horizon atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
        ({(b : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hsplit : paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ) =
      (paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ)) ∪
      ((paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
        ({(b : ℝ)} : Set ℝ)) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Iio, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hp, ht⟩
      rcases lt_or_eq_of_le ht with hlt | heq
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨⟨hp, ht⟩, heq⟩
    · rintro (⟨hp, ht⟩ | ⟨⟨hp, ht⟩, _⟩)
      · exact ⟨hp, le_of_lt ht⟩
      · exact ⟨hp, ht⟩
  have hdisj : Disjoint (paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ))
      ((paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
        ({(b : ℝ)} : Set ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t ht hEq
    have heq : t = (b : ℝ) := hEq.2
    subst t
    exact (lt_irrefl (b : ℝ)) ht.2
  have hparts :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
          ({(b : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    conv_lhs => rw [hsplit]
    exact lintegral_union
      (((paymentTimes_measurable _).inter measurableSet_Iic).inter
        (measurableSet_singleton (b : ℝ))) hdisj
  have hfin := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    D hD.1.1 ω (ruinTime X x D ω) b q hq
  have hpfin := ENNReal.add_lt_top.mp (by rw [← hparts]; exact hfin)
  rw [hparts, ENNReal.toReal_add hpfin.1.ne hpfin.2.ne]
