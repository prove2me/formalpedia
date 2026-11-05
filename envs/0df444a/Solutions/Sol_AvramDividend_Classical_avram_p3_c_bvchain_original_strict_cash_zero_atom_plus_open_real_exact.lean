-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:58:10.660205+00:00
-- url     : https://prove2.me/submissions/7d696e0e-793b-4458-944d-ae53a4247b50

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact original real strictly stopped cash is the initial right payment plus all open-horizon cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) (hb : 0 < b) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hzero := (avram_wave7_19_original_ruin_endpoint_exclusion_and_time_zero_payment X x D ω).1
  have hsplit : paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ) =
      ({0} : Set ℝ) ∪ (paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ)) := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioo, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hp, ht⟩
      rcases lt_or_eq_of_le (paymentTimes_membership_to_nNReal_active _ t hp).1 with hpos | heq
      · exact Or.inr ⟨hp, hpos, ht⟩
      · exact Or.inl heq.symm
    · rintro (rfl | ⟨hp, _, ht⟩)
      · exact ⟨hzero, hbR⟩
      · exact ⟨hp, ht⟩
  have hdisjoint : Disjoint ({0} : Set ℝ)
      (paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t ht0 htpos; subst t
    exact (not_lt_of_ge (le_refl (0 : ℝ))) htpos.2.1
  have hparts :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [hsplit]
    exact lintegral_union ((paymentTimes_measurable _).inter measurableSet_Ioo) hdisjoint
  have hclosed := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite D hD.1.1 ω (ruinTime X x D ω) b q hq
  have hfinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono_set ?_) hclosed
    intro t ht
    exact ⟨ht.1, mem_Iic.mpr (le_of_lt (mem_Iio.mp ht.2))⟩
  have hfinparts := ENNReal.add_lt_top.mp (by rw [← hparts]; exact hfinite)
  have hZeroSet : paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) =
      ({0} : Set ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_singleton_iff]
    constructor
    · rintro ⟨hp, ht⟩
      exact le_antisymm ht (paymentTimes_membership_to_nNReal_active _ t hp).1
    · rintro rfl
      exact ⟨hzero, le_refl 0⟩
  obtain ⟨_, hAtom, hδ⟩ :=
    avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton X x D hD.1.1 w hjump ω
  have hZeroInt := avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom D ω (ruinTime X x D ω) q
  rw [hZeroSet] at hZeroInt
  rw [hparts, ENNReal.toReal_add hfinparts.1.ne hfinparts.2.ne]
  rw [hZeroInt, hAtom, ENNReal.toReal_ofReal hδ]
