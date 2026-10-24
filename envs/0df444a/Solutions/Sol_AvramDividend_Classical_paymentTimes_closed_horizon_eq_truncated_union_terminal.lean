-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_closed_horizon_eq_truncated_union_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:16:01.994453+00:00
-- url     : https://prove2.me/submissions/2aeee08f-ccf0-4aa7-8d57-b6fd865518a1

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A stopped clock excludes the final positive time; this identity
    restores its Stieltjes payment atom, including the zero-horizon case. -/
theorem solution (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Set.Iic T =
      paymentTimes (min σ (ENNReal.ofReal T)) ∪
        (paymentTimes σ ∩ ({T} : Set ℝ)) := by
  rcases lt_or_eq_of_le hT with hpos | hzero
  · rw [paymentTimes_min_ofReal_eq_inter_Iio_of_pos σ T hpos]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Iio,
      Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨htσ, htle⟩
      rcases lt_or_eq_of_le htle with hlt | heq
      · exact Or.inl ⟨htσ, hlt⟩
      · exact Or.inr ⟨htσ, heq⟩
    · intro ht
      rcases ht with ⟨htσ, hlt⟩ | ⟨htσ, heq⟩
      · exact ⟨htσ, le_of_lt hlt⟩
      · exact ⟨htσ, le_of_eq heq⟩
  · subst T
    rw [ENNReal.ofReal_zero, paymentTimes_min_zero_eq_singleton_zero σ]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_union,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨htσ, htle⟩
      exact Or.inl (le_antisymm htle htσ.1)
    · intro ht
      rcases ht with hz | ⟨htσ, hz⟩
      · subst t
        exact ⟨⟨le_refl _, Or.inl rfl⟩, le_refl _⟩
      · subst t
        exact ⟨htσ, le_refl _⟩
