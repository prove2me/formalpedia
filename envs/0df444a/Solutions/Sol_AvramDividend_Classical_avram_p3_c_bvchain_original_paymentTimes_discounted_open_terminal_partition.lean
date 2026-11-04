-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:27:36.39158+00:00
-- url     : https://prove2.me/submissions/1f9e7daf-1f59-4d98-9789-78b763d8734a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original stopped payment-time Stieltjes partition: the middle right
payment is counted once and the external right payments are excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b c : ℝ≥0) (hab : a < b) (hbc : b < c) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (b : ℝ) (c : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hbcR : (b : ℝ) < (c : ℝ) := by exact_mod_cast hbc
  have hsplit : paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (c : ℝ) =
      (paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ)) ∪
      (paymentTimes (ruinTime X x D ω) ∩ Ioo (b : ℝ) (c : ℝ)) := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Ioc, mem_union]
    constructor
    · rintro ⟨hp, hta, htc⟩
      by_cases htb : t ≤ (b : ℝ)
      · exact Or.inl ⟨hp, hta, htb⟩
      · exact Or.inr ⟨hp, lt_of_not_ge htb, htc⟩
    · rintro (⟨hp, hta, htb⟩ | ⟨hp, htb, htc⟩)
      · exact ⟨hp, hta, lt_of_le_of_lt htb hbcR⟩
      · exact ⟨hp, lt_trans habR htb, htc⟩
  have hdisjoint : Disjoint
      (paymentTimes (ruinTime X x D ω) ∩ Ioc (a : ℝ) (b : ℝ))
      (paymentTimes (ruinTime X x D ω) ∩ Ioo (b : ℝ) (c : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t hleft hright
    exact (not_lt_of_ge hleft.2.2) hright.2.1
  rw [hsplit]
  exact lintegral_union
    ((paymentTimes_measurable _).inter measurableSet_Ioo) hdisjoint
