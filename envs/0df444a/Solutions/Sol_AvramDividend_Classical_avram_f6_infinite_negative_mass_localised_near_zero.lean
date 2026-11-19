-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_infinite_negative_mass_localised_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:29:36.871432+00:00
-- url     : https://prove2.me/submissions/35083c7c-b4d6-4ee6-96ba-602f86349a57

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hTotal : ν (Iio (0 : ℝ)) = ⊤)
    (hTail : ν (Iic (-δ)) < ⊤) :
    ν (Ioo (-δ) 0) = ⊤ := by
  have hSet : Iio (0 : ℝ) = Iic (-δ) ∪ Ioo (-δ) 0 := by
    ext y
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro hy
      by_cases hh : y ≤ -δ
      · exact Or.inl hh
      · exact Or.inr ⟨lt_of_not_ge hh, hy⟩
    · intro hy
      rcases hy with hh | hh
      · exact lt_of_le_of_lt hh (neg_neg_of_pos hδ)
      · exact hh.2
  have hDisjoint : Disjoint (Iic (-δ)) (Ioo (-δ) 0) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    exact (not_lt_of_ge h1) h2.1
  have hSum : ν (Iic (-δ)) + ν (Ioo (-δ) 0) = ⊤ := by
    rw [← measure_union hDisjoint measurableSet_Ioo]
    simpa only [← hSet] using hTotal
  by_contra hFinite
  have hSmall : ν (Ioo (-δ) 0) < ⊤ :=
    lt_top_iff_ne_top.mpr hFinite
  have hAdd : ν (Iic (-δ)) + ν (Ioo (-δ) 0) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hTail, hSmall⟩
  rw [hSum] at hAdd
  exact (lt_irrefl (⊤ : ℝ≥0∞)) hAdd
