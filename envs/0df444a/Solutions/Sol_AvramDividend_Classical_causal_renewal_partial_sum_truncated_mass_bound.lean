-- Prove2me | solution 1 for AvramDividend.Classical.causal_renewal_partial_sum_truncated_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:08:09.917972+00:00
-- url     : https://prove2.me/submissions/e48bc00b-d723-48fc-9ba6-9f346a25a1b2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem solution
    (F : ℕ → ℝ → ℝ) (ρ b : ℝ)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hbound : ∀ n : ℕ,
      (∫ t in Ioc (0 : ℝ) b, F n t ∂volume) ≤ ρ ^ (n + 1))
    (s : Finset ℕ) :
    (∫ t in Ioc (0 : ℝ) b, ∑ n ∈ s, F n t ∂volume) ≤
      ∑ n ∈ s, ρ ^ (n + 1) := by
  rw [integral_finset_sum s fun n _ => (hFi n).mono_set Ioc_subset_Ioi_self]
  exact Finset.sum_le_sum fun n _ => hbound n
