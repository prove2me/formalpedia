-- Prove2me | solution 2 for AvramDividend.Classical.causal_gaussian_weighted_series_identification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:52:01.745864+00:00
-- url     : https://prove2.me/submissions/0579f255-a496-4c7a-aaf9-84a0755d2ddb

import Mathlib
open MeasureTheory Set

theorem solution
    (P H : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a w : ℝ)
    (hH : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume)) / a)
    (hg : g = fun y : ℝ => 1 / a + Real.exp (w * y) *
      (∑' n : ℕ, (Real.exp (-w * y) *
        (∫ t in Ioc (0 : ℝ) y,
          Real.exp (w * t) * P n t ∂volume)) / a)) :
    ∃ Q : ℕ → ℝ → ℝ,
      Q 0 = (fun _ : ℝ => 1 / a) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => Real.exp (w * x) * H n x) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => (1 / a) *
          (∫ t in Ioc (0 : ℝ) x,
            Real.exp (w * t) * P n t ∂volume)) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => Q n x) →
        g x = ∑' n : ℕ, Q n x) := by
  have key : ∀ x : ℝ, Real.exp (w * x) * (Real.exp (-w * x)) = 1 := by
    intro x; rw [← Real.exp_add]; ring_nf; simp
  refine ⟨fun n => Nat.casesOn n (fun _ => 1 / a) (fun m x => (1 / a) *
      (∫ t in Ioc (0 : ℝ) x, Real.exp (w * t) * P m t ∂volume)), rfl, ?_, fun n => rfl, ?_⟩
  · intro n; funext x; rw [hH]; simp only
    rw [← mul_div_assoc, ← mul_assoc, key]; ring
  · intro x hs
    rw [hs.tsum_eq_zero_add, hg]
    simp only
    rw [← tsum_mul_left]
    congr 1
    refine tsum_congr fun n => ?_
    rw [← mul_div_assoc, ← mul_assoc, key]; ring
