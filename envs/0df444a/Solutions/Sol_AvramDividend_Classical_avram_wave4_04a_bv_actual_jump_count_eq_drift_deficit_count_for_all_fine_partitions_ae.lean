-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:38:36.905208+00:00
-- url     : https://prove2.me/submissions/6de6f9fb-6d5a-4c76-b546-5e766014d02b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        StrictMono grid → grid 0 = 0 → grid n = T →
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
        ({i : ℕ | i < n ∧
          X.X (grid (i + 1)) ω - X.X (grid i) ω <
            X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))}.ncard :
          ENNReal) := by
  have hFine :=
    avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
      X hBV hFinite T hT
  have hOccupied :=
    avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
      X hBV hFinite T hT
  filter_upwards [hFine, hOccupied] with ω hfω hoω
  obtain ⟨δ, hδ, hf⟩ := hfω
  refine ⟨δ, hδ, ?_⟩
  intro n grid hStrict hZero hEnd hWidth
  have hBounds : ∀ i : ℕ, i < n →
      grid i ≤ grid (i + 1) ∧ grid (i + 1) ≤ T := by
    intro i hi
    constructor
    · exact hStrict.monotone (Nat.le_succ i)
    · have hin : i + 1 ≤ n := by omega
      simpa only [hEnd] using (hStrict.monotone hin)
  have hSets :
      {i : ℕ | i < n ∧ ∃ u : ℝ≥0,
        u ≤ T ∧ 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        u ∈ Ioc (grid i) (grid (i + 1))} =
      {i : ℕ | i < n ∧ ∃ u : ℝ≥0,
        u ∈ Ioc (grid i) (grid (i + 1)) ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
    ext i
    constructor
    · rintro ⟨hi, u, huT, hu0, hjump, hcell⟩
      exact ⟨hi, u, hcell, hjump⟩
    · rintro ⟨hi, u, hcell, hjump⟩
      have huT : u ≤ T := le_trans hcell.2 (hBounds i hi).2
      have hu0 : 0 < u :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ grid i from zero_le) hcell.1
      exact ⟨hi, u, huT, hu0, hjump, hcell⟩
  have hEq := hf n grid hStrict hZero hEnd hWidth
  rw [hSets, hoω n grid hBounds] at hEq
  exact hEq
