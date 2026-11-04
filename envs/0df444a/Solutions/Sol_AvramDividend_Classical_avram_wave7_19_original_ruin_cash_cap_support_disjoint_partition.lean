-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ruin_cash_cap_support_disjoint_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:46:15.2102+00:00
-- url     : https://prove2.me/submissions/889e0103-1a2a-4706-bd25-86c8ad578715

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Split original strictly killed cash into boundary-supported and complementary mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (hBoundary : MeasurableSet boundary) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) \ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let s : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T
  have hs : MeasurableSet s :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  have hb : MeasurableSet (s \ boundary) := hs.diff hBoundary
  have hd : Disjoint (s ∩ boundary) (s \ boundary) := by
    refine Set.disjoint_left.mpr ?_
    intro t ht hd
    exact hd.2 ht.2
  have hpart : s = (s ∩ boundary) ∪ (s \ boundary) := by
    ext t
    constructor
    · intro ht
      by_cases h : t ∈ boundary
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    · rintro (ht | ht)
      · exact ht.1
      · exact ht.1
  change (∫⁻ t in s,
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in s ∩ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in s \ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  calc
    _ = ∫⁻ t in (s ∩ boundary) ∪ (s \ boundary),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) := by
            simpa only [← hpart]
    _ = _ := lintegral_union hb hd
