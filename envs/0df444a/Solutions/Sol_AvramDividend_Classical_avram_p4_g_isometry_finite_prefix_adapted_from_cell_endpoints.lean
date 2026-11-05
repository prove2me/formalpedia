-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_adapted_from_cell_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:26:15.183338+00:00
-- url     : https://prove2.me/submissions/32513404-d5fc-43a8-afa0-2f62320583ad

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal BigOperators
noncomputable section

/-- Chronological right-endpoint adapted cells give original finite adapted prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0)
    (hEarlier : ∀ i n, i < n → grid (i + 1) ≤ grid n)
    (D : ℕ → Ω → ℝ)
    (hCell : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))] (D i))
    (n : ℕ) :
    StronglyMeasurable[𝓕 (grid n)]
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by
  classical
  have hSum : StronglyMeasurable[𝓕 (grid n)]
      (∑ i ∈ Finset.range n, D i) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    exact (hCell i).mono (𝓕.mono (hEarlier i n (Finset.mem_range.mp hi)))
  have hEq :
      (∑ i ∈ Finset.range n, D i) =
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [← hEq]
  exact hSum
