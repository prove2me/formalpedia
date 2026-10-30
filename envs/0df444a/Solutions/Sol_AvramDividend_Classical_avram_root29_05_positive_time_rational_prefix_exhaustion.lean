-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_positive_time_rational_prefix_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:43:33.624331+00:00
-- url     : https://prove2.me/submissions/9475c0ba-48d2-487f-a7d7-3a8144a936a1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal Classical

/-- Finite half-open rational prefixes exhaust every strictly positive
payment time under an arbitrary nonnegative Stieltjes integral. -/
theorem solution (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (n : ℕ) :
    (∫⁻ r in Ioi (0 : ℝ), f r ∂μ) =
      ⨆ N : ℕ, (∫⁻ r in Ioc (0 : ℝ)
        ((N : ℝ) / ((n : ℝ) + 1)), f r ∂μ) := by
  let u : ℕ → ℝ := fun N => (N : ℝ) / ((n : ℝ) + 1)
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hp.le
  have hd : Directed (fun (a b : Set ℝ) => a ⊆ b)
      (fun N : ℕ => Ioc (0 : ℝ) (u N)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro r hr
      exact ⟨hr.1, hr.2.trans (hu (le_max_left i j))⟩
    · intro r hr
      exact ⟨hr.1, hr.2.trans (hu (le_max_right i j))⟩
  have hU : (⋃ N : ℕ, Ioc (0 : ℝ) (u N)) = Ioi 0 := by
    apply (iUnion_Ioc_eq_Ioi_self_iff).2
    intro r hr
    obtain ⟨N, hN⟩ := exists_nat_ge (r * ((n : ℝ) + 1))
    refine ⟨N, ?_⟩
    exact (le_div_iff₀ hp).2 hN
  rw [← hU]
  simpa [u] using (setLIntegral_iUnion_of_directed f hd)
