-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_positive_semigroup_exp_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:21:34.947362+00:00
-- url     : https://prove2.me/submissions/500d0825-622b-4f57-ad61-70f9eee468e6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_nonnegative_additive_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A positive multiplicative semigroup whose logarithm is continuous at
height zero is the exponential of its unit-height logarithm. -/
theorem solution
    (F : ℝ → ℝ)
    (hpos : ∀ t : ℝ, 0 < t → 0 < F t)
    (hsem : ∀ s t : ℝ, 0 < s → 0 < t →
      F (s + t) = F s * F t)
    (hcont : ContinuousAt (fun t : ℝ =>
      if 0 < t then Real.log (F t) else 0) 0) :
    ∀ h : ℝ, 0 < h →
      F h = Real.exp (h * Real.log (F 1)) := by
  let g : ℝ → ℝ := fun t =>
    if 0 < t then Real.log (F t) else 0
  have hgzero : g 0 = 0 := by simp [g]
  have hgadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      g (x + y) = g x + g y := by
    intro x y hx hy
    by_cases hx0 : x = 0
    · subst x
      simp only [zero_add, g, lt_irrefl, ↓reduceIte, zero_add]
    by_cases hy0 : y = 0
    · subst y
      simp only [add_zero, g, lt_irrefl, ↓reduceIte, add_zero]
    have hxp : 0 < x := by
      rcases eq_or_lt_of_le hx with h | h
      · exact (hx0 h.symm).elim
      · exact h
    have hyp : 0 < y := by
      rcases eq_or_lt_of_le hy with h | h
      · exact (hy0 h.symm).elim
      · exact h
    have hxyp : 0 < x + y := add_pos hxp hyp
    change (if 0 < x + y then Real.log (F (x + y)) else 0) =
      (if 0 < x then Real.log (F x) else 0) +
      (if 0 < y then Real.log (F y) else 0)
    rw [if_pos hxyp, if_pos hxp, if_pos hyp, hsem x y hxp hyp]
    exact Real.log_mul (ne_of_gt (hpos x hxp)) (ne_of_gt (hpos y hyp))
  have hgcont : ContinuousAt g 0 := hcont
  have hlinear := avram_wave3_01_nonnegative_additive_linear
    g hgzero hgadd hgcont
  intro h hh
  have hlog : Real.log (F h) = h * Real.log (F 1) := by
    have h := hlinear h hh.le
    simpa only [g, if_pos hh, if_pos (by norm_num : (0 : ℝ) < 1)]
      using h
  calc
    F h = Real.exp (Real.log (F h)) :=
      (Real.exp_log (hpos h hh)).symm
    _ = Real.exp (h * Real.log (F 1)) := by rw [hlog]
