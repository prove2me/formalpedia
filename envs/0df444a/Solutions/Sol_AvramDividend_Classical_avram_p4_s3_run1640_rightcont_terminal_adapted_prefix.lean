-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_rightcont_terminal_adapted_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:02:20.751199+00:00
-- url     : https://prove2.me/submissions/e6f45f8d-5c9a-4acc-afff-0ad730e13b07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Completed adapted increments form a predictable prefix at each future grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (D : ℕ → Ω → ℝ)
    (hTerminal : ∀ j,
      StronglyMeasurable[𝓕.rightCont (grid (j + 1))] (D j)) :
    ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω) := by
  classical
  have hGridMono : Monotone grid := monotone_nat_of_le_succ hGrid
  intro i
  have hOne (j : ℕ) (hji : j < i) :
      StronglyMeasurable[𝓕.rightCont (grid i)] (D j) := by
    have hTime : grid (j + 1) ≤ grid i :=
      hGridMono (Nat.succ_le_of_lt hji)
    exact (hTerminal j).mono ((𝓕.rightCont).mono hTime)
  have hSum : StronglyMeasurable[𝓕.rightCont (grid i)]
      (∑ j ∈ Finset.range i, D j) := by
    apply Finset.stronglyMeasurable_sum
    intro j hj
    exact hOne j (Finset.mem_range.mp hj)
  have hEq : (∑ j ∈ Finset.range i, D j) =
      (fun ω => ∑ j ∈ Finset.range i, D j ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [← hEq]
  exact hSum
