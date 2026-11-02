-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_tapered_envelope_log_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:23:21.562317+00:00
-- url     : https://prove2.me/submissions/6c19f0c0-d416-418a-8a23-659b742c5a95

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! A tapered profile dominated by a logarithmically bounded quotient
retains the same BV logarithmic bound on the full positive unit interval. -/
theorem solution
    (f : ℝ → ℝ) (G : C(unitInterval.Elem, ℝ))
    (a K : ℝ) (hK : 0 ≤ K)
    (hzero : ∀ t : unitInterval.Elem, (t : ℝ) ≤ a → G t = 0)
    (hbound : ∀ t : unitInterval.Elem,
      |G t| ≤ |f (max a (min (t : ℝ) 1))|)
    (hf : ∀ t : ℝ, a ≤ t → t ≤ 1 →
      |(1 - t) * f t| ≤ K * |Real.log t|) :
    ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ K * |Real.log (t : ℝ)| := by
  intro t ht
  by_cases hta : (t : ℝ) ≤ a
  · rw [hzero t hta]
    simp only [mul_zero, abs_zero]
    exact mul_nonneg hK (abs_nonneg _)
  · have hat : a ≤ (t : ℝ) := le_of_lt (lt_of_not_ge hta)
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hclamp : max a (min (t : ℝ) 1) = (t : ℝ) := by
      rw [min_eq_left ht1, max_eq_right hat]
    have hGb : |G t| ≤ |f (t : ℝ)| := by
      simpa only [hclamp] using hbound t
    calc
      |(1 - (t : ℝ)) * G t| =
          |1 - (t : ℝ)| * |G t| := abs_mul _ _
      _ ≤ |1 - (t : ℝ)| * |f (t : ℝ)| :=
          mul_le_mul_of_nonneg_left hGb (abs_nonneg _)
      _ = |(1 - (t : ℝ)) * f (t : ℝ)| := (abs_mul _ _).symm
      _ ≤ K * |Real.log (t : ℝ)| := hf (t : ℝ) hat ht1
