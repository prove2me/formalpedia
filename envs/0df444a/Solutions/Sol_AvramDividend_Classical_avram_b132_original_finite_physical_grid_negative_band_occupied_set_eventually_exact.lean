-- Prove2me | solution 1 for AvramDividend.Classical.avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:57:17.564825+00:00
-- url     : https://prove2.me/submissions/bfa06aaf-5920-46f2-9c2c-e65627a6335c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Cutoff-band occupation of any finite original physical clock grid eventually agrees exactly with all actual marked cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      S.filter (fun i => ∃ u : ℝ≥0,
        s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) =
      S.filter (fun i => ∃ u : ℝ≥0,
        s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) := by
  classical
  let F : Finset ℕ := S.filter (fun i => ∃ u : ℝ≥0,
    s i < u ∧ u ≤ t i ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
  let J : ℕ → Finset ℕ := fun n => S.filter (fun i => ∃ u : ℝ≥0,
    s i < u ∧ u ≤ t i ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))
  have hMarked : ∀ i ∈ F, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨N, hN⟩ :=
    avram_b118_original_finite_physically_marked_cells_one_cutoff
      X ω F s t hMarked
  have hSub (n : ℕ) : J n ⊆ F := by
    intro i hi
    obtain ⟨hiS, u, hsu, hut, hb⟩ := Finset.mem_filter.mp hi
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact Finset.mem_filter.mpr ⟨hiS, u, hsu, hut, by linarith⟩
  have hMono : ∀ n m, n ≤ m → J n ⊆ J m := by
    intro n m hnm i hi
    obtain ⟨hiS, u, hsu, hut, hb⟩ := Finset.mem_filter.mp hi
    have hIncl :=
      avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
        X ω (s i) (t i) n m hnm
    obtain ⟨_, _, hb'⟩ := hIncl ⟨hsu, hut, hb⟩
    exact Finset.mem_filter.mpr ⟨hiS, u, hsu, hut, hb'⟩
  refine ⟨N, ?_⟩
  intro n hn
  change J n = F
  apply Finset.Subset.antisymm (hSub n)
  intro i hi
  exact hMono N n hn
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hN i hi⟩)
