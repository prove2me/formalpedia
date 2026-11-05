-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_prefix_adapted_from_endpoint_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:27:08.5595+00:00
-- url     : https://prove2.me/submissions/4d3b29e8-bbb7-4c65-b4b8-f4022d8467de

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal BigOperators
noncomputable section

/-- Original endpoint-adapted count cells with predictable weights form adapted finite prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H J D : ℕ → Ω → ℝ) (r : ℕ → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * (J i ω - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hJ : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))] (J i))
    (n : ℕ) :
    StronglyMeasurable[𝓕 (grid n)]
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by
  classical
  letI : MeasurableSpace Ω := 𝓕 (grid n)
  have hMon : Monotone grid := monotone_nat_of_le_succ hGrid
  have hSum : StronglyMeasurable[𝓕 (grid n)]
      (∑ i ∈ Finset.range n, D i) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hEnd : grid (i + 1) ≤ grid n :=
      hMon (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hHi : StronglyMeasurable[𝓕 (grid n)] (H i) :=
      (hH i).mono (𝓕.mono (le_trans (hGrid i) hEnd))
    have hJi : StronglyMeasurable[𝓕 (grid n)] (J i) :=
      (hJ i).mono (𝓕.mono hEnd)
    have hProduct : StronglyMeasurable[𝓕 (grid n)]
        (fun ω => H i ω * (J i ω - r i)) :=
      hHi.mul (hJi.sub stronglyMeasurable_const)
    have hEq : D i = fun ω => H i ω * (J i ω - r i) := by
      funext ω
      exact hD i ω
    rw [hEq]
    exact hProduct
  have hEqSum :
      (∑ i ∈ Finset.range n, D i) =
      (fun ω => ∑ i ∈ Finset.range n, D i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [← hEqSum]
  exact hSum
