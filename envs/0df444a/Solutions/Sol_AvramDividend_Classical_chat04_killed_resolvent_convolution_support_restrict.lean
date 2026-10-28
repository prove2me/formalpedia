-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_convolution_support_restrict
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:35:31.226857+00:00
-- url     : https://prove2.me/submissions/446d38d9-595b-42b2-9c69-8f252292f0e5

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem solution
    (x : ℝ) (hx : 0 ≤ x) (Wq Wqp : ℝ → ℝ)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0) :
    (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
    (∫ y in Ioc (0 : ℝ) x, Wq y * Wqp (x - y)) := by 
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self ?_
  intro y hy
  have : x < y := by
    rcases hy with ⟨h1, h2⟩
    simp only [Set.mem_Ioc, not_and, not_le] at h2
    exact h2 h1
  rw [hzero (x - y) (by linarith), mul_zero]
