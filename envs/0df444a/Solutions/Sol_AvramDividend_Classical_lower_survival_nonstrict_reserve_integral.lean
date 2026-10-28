-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_nonstrict_reserve_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:53:33.0051+00:00
-- url     : https://prove2.me/submissions/04f7cd94-7d8e-4dac-8c7f-c3dad40eaf0f

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Reserve integration with the weak survival inequality equals the
exponential tail: the possible equality boundary is Lebesgue-null. -/
theorem solution (m θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧ 0 ≤ x + m}, Real.exp (-θ * x)) =
      Real.exp (-θ * max 0 (-m)) / θ := by
  have hn : -θ < 0 := by linarith
  by_cases hm : 0 ≤ m
  · have hset : {x : ℝ | 0 < x ∧ 0 ≤ x + m} = Ioi 0 := by
      ext x
      simp only [mem_setOf_eq, mem_Ioi]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, by linarith⟩
    have hmax : max (0 : ℝ) (-m) = 0 := max_eq_left (by linarith)
    rw [hset, hmax]
    have hi := integral_exp_mul_Ioi hn (0 : ℝ)
    simpa only [neg_div_neg_eq] using hi
  · have hmneg : 0 < -m := by linarith
    have hset : {x : ℝ | 0 < x ∧ 0 ≤ x + m} = Ici (-m) := by
      ext x
      simp only [mem_setOf_eq, mem_Ici]
      constructor
      · intro hx
        linarith [hx.2]
      · intro hx
        constructor <;> linarith
    have hmax : max (0 : ℝ) (-m) = -m :=
      max_eq_right (le_of_lt hmneg)
    rw [hset, integral_Ici_eq_integral_Ioi, hmax]
    have hi := integral_exp_mul_Ioi hn (-m)
    simpa only [neg_div_neg_eq] using hi
