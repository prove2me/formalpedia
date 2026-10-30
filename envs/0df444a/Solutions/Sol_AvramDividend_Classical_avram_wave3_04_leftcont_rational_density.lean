-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_leftcont_rational_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:33:47.821808+00:00
-- url     : https://prove2.me/submissions/ab54e0fd-f3f3-416a-af60-bd8023ddd474

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal NNRat

/-- A monotone left-continuous path attains every strict upper level
at an earlier nonnegative rational time. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hm : Monotone f)
    (hc : ∀ t, ContinuousWithinAt f (Set.Iic t) t)
    (t : ℝ≥0) (a : ℝ)
    (ht : t ≠ 0) (ha : a < f t) :
    ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < f (r : ℝ≥0) := by
  have hpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
  letI : (nhdsWithin t (Set.Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  have hc' : ContinuousWithinAt f (Set.Iio t) t :=
    (hc t).mono (by
      intro s hs
      exact le_of_lt (Set.mem_Iio.mp hs))
  have hev : ∀ᶠ s in nhdsWithin t (Set.Iio t), a < f s :=
    hc'.eventually (isOpen_Ioi.mem_nhds ha)
  have hev_lt : ∀ᶠ s in nhdsWithin t (Set.Iio t), s < t :=
    self_mem_nhdsWithin
  obtain ⟨s, hslt, hsval⟩ := (hev_lt.and hev).exists
  rcases (NNReal.lt_iff_exists_rat_btwn s t).mp hslt with
    ⟨q, hq0, hqs, hqt⟩
  let r : ℚ≥0 := ⟨q, hq0⟩
  have hqreal : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have heq : (r : ℝ≥0) = (q : ℝ).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hqreal]
    change ((⟨q, hq0⟩ : ℚ≥0) : ℝ) = (q : ℝ)
    exact NNRat.cast_mk q hq0
  refine ⟨r, ?_, ?_⟩
  · simpa [heq] using hqt
  · exact lt_of_lt_of_le hsval (hm (le_of_lt (by simpa [heq] using hqs)))
