-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_closed_horizon_discounted_cash_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:31:58.515821+00:00
-- url     : https://prove2.me/submissions/a52e59c9-6d76-45be-97a7-872b6edb9942

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On the original dividend measure, the closed horizon includes precisely the
    additional payment atom at the horizon if this precedes ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (ω : Ω)
    (hPaid : MeasurableSet (paymentTimes (ruinTime X x D ω))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := paymentTimes (ruinTime X x D ω)
  have hsplit : A ∩ Iic T = (A ∩ Iio T) ∪ (A ∩ {T}) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_union,
      Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, hle⟩
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inl ⟨ha, hlt⟩
      · exact Or.inr ⟨ha, heq⟩
    · rintro (⟨ha, hlt⟩ | ⟨ha, heq⟩)
      · exact ⟨ha, le_of_lt hlt⟩
      · exact ⟨ha, le_of_eq heq⟩
  have hdisjoint : Disjoint (A ∩ Iio T) (A ∩ {T}) := by
    apply Set.disjoint_left.mpr
    intro t ht hu
    have hlt : t < T := ht.2
    have heq : t = T := by simpa using hu.2
    exact (ne_of_lt hlt) heq
  change (∫⁻ t in A ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in A ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in A ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  rw [hsplit]
  exact lintegral_union (hPaid.inter (measurableSet_singleton T)) hdisjoint
