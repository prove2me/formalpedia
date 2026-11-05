-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_prefix_predictable_of_adapted_finite_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:00:41.084027+00:00
-- url     : https://prove2.me/submissions/9382763b-0e9e-4ece-9c55-5badc03ade12

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal Nat BigOperators

/-- Earlier adapted compensated cells produce a predictable prefix sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hFilt : ∀ {i j : ℕ}, i ≤ j →
      𝓕 (grid i) ≤ 𝓕 (grid j))
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hKpast : ∀ i, Measurable[𝓕 (grid (i + 1))]
      (fun ω => (K i ω : ℝ)))
    (n : ℕ) :
    Measurable[𝓕 (grid n)] (fun ω =>
      ∑ i ∈ Finset.range n, H i ω *
        ((K i ω : ℝ) - (r i : ℝ))) := by
  apply Finset.measurable_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hHn : Measurable[𝓕 (grid n)] (H i) :=
    (hH i).mono (hFilt (Nat.le_of_lt hin)) le_rfl
  have hKn : Measurable[𝓕 (grid n)]
      (fun ω => (K i ω : ℝ)) :=
    (hKpast i).mono (hFilt (Nat.succ_le_of_lt hin)) le_rfl
  exact hHn.mul (hKn.sub measurable_const)
