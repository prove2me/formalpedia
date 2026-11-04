-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_marked_grid_eventual_occupation_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:16:21.67152+00:00
-- url     : https://prove2.me/submissions/8ef1447d-4751-43ff-9f29-c344e3efce16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_NNReal_marked_times_pairwise_gap
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_marked_grid_single_occupation_of_mesh_lt_gap
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

/-- Eventual exact grid count for the same original marked-jump sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (k : ℕ)
    (S : Set ℝ≥0)
    (hS : S = {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((k : ℝ) + 1))})
    (grid : ℕ → ℕ → ℝ≥0)
    (hMono : ∀ m, Monotone (grid m))
    (hCover : ∀ᶠ m in (Filter.atTop : Filter ℕ),
      ∀ u : ℝ≥0, u ∈ S →
        ∃ i : ℕ, i < m ∧ u ∈ Ioc (grid m i) (grid m (i + 1)))
    (hFine : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in (Filter.atTop : Filter ℕ),
        ∀ i < m, (grid m (i + 1) : ℝ) - (grid m i : ℝ) < δ) :
    ∀ᶠ m in (Filter.atTop : Filter ℕ),
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) =
      (((Finset.range m).filter (fun i =>
        ∃ u : ℝ≥0, u ∈ S ∧
          u ∈ Ioc (grid m i) (grid m (i + 1)))).card : ℝ≥0∞) := by
  classical
  have hFin : S.Finite := by
    rw [hS]
    exact avram_wave7_06_original_negative_band_marked_times_finite
      X ω T k
  let F : Finset ℝ≥0 := hFin.toFinset
  have hF (u : ℝ≥0) : u ∈ F ↔ u ∈ S :=
    Set.Finite.mem_toFinset hFin
  obtain ⟨δ, hδ, hGap⟩ :=
    avram_wave7_06_finite_NNReal_marked_times_pairwise_gap F
  filter_upwards [hFine δ hδ, hCover] with m hm hmCover
  have hSingle : ∀ i : ℕ, i < m → ∀ u v : ℝ≥0,
      u ∈ S → v ∈ S →
      u ∈ Ioc (grid m i) (grid m (i + 1)) →
      v ∈ Ioc (grid m i) (grid m (i + 1)) → u = v := by
    intro i hi u v hu hv huCell hvCell
    exact avram_wave7_06_marked_grid_single_occupation_of_mesh_lt_gap
      F δ hδ hGap (grid m) m hm
      i hi u ((hF u).mpr hu) v ((hF v).mpr hv) huCell hvCell
  have hUnique : ∀ u : ℝ≥0, u ∈ S → ∀ i j : ℕ,
      i < m → j < m →
      u ∈ Ioc (grid m i) (grid m (i + 1)) →
      u ∈ Ioc (grid m j) (grid m (j + 1)) → i = j := by
    intro u hu i j hi hj hiCell hjCell
    exact avram_wave7_06_monotone_marked_grid_index_unique
      (grid m) (hMono m) u i j hiCell hjCell
  exact avram_wave7_06_original_negative_band_grid_occupied_card_of_unique_source_cover
    X ω T k m (grid m) S hS hmCover hSingle hUnique
