-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_head_tail_global_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:11:23.284951+00:00
-- url     : https://prove2.me/submissions/ccafd35f-46c1-4338-bc9f-869a2a509826

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Positive Gaussian head and tail recurrence extends across zero to the whole real line. -/
theorem solution
    (a : ℝ) (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hhead : ∀ x : ℝ, 0 < x →
      Q 1 x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q 0 s ∂volume))
    (htail : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      Q (n + 2) x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q (n + 1) s ∂volume))
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0) :
    ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)) := by
  intro n
  funext x
  change Q (n + 1) x = -((1 / a) *
    (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume))
  by_cases hx : 0 < x
  · cases n with
    | zero => simpa only [zero_add, neg_mul] using hhead x hx
    | succ n =>
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, neg_mul] using htail n x hx
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    rw [hzero n x hx0, Ioc_eq_empty_of_le hx0]
    simp
