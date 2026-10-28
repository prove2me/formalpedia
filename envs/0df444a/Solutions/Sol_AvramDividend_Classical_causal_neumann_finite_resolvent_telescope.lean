-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_finite_resolvent_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:12:19.754671+00:00
-- url     : https://prove2.me/submissions/4246c72d-d92a-4f8d-a864-3cb3a6948e55

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A finite Neumann correction telescopes under exact operator additivity. -/
theorem solution
    (F : ℝ → ℝ) (T : (ℝ → ℝ) → (ℝ → ℝ))
    (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) = -T (Q n))
    (hlinear : ∀ n : ℕ,
      T (∑ i ∈ Finset.range (n + 1), Q i) =
        ∑ i ∈ Finset.range (n + 1), T (Q i))
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Q i) +
      T (∑ i ∈ Finset.range (n + 1), Q i) =
        F - Q (n + 1) := by
  classical
  have hT (i : ℕ) : T (Q i) = -Q (i + 1) := by
    rw [hstep i]
    simp
  have hfinite (m : ℕ) :
      (∑ i ∈ Finset.range m, Q i) +
        (∑ i ∈ Finset.range m, T (Q i)) =
          F - Q m := by
    induction m with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, zero_add]
        rw [hzero]
        abel
    | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, hT m]
        calc
          ((∑ i ∈ Finset.range m, Q i) + Q m) +
              ((∑ i ∈ Finset.range m, T (Q i)) + -Q (m + 1)) =
            ((∑ i ∈ Finset.range m, Q i) +
              (∑ i ∈ Finset.range m, T (Q i))) +
                Q m - Q (m + 1) := by abel
          _ = (F - Q m) + Q m - Q (m + 1) := by rw [ih]
          _ = F - Q (m + 1) := by abel
  rw [hlinear n]
  exact hfinite (n + 1)
