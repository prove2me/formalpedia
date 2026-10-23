-- Prove2me | solution 1 for BrumelleMcGill1993.thm2_exists_optimal_integer_policy_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:37:43.305479+00:00
-- url     : https://prove2.me/submissions/d9e8315d-58ac-4a64-bd0e-7f4b76c60dc5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_exists_optimal_integer_policy

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, IsOptimal P X f (fun k => (p k : ℝ)) := by
  obtain ⟨p, hp, -⟩ := theorem2_exists_optimal_integer_policy P X f hM hint hpos
  exact ⟨p, hp⟩
