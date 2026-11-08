-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_finset_stable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:57:13.470907+00:00
-- url     : https://prove2.me/submissions/85d9c935-7d9c-4ac6-a5f3-d03cb03ad9f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (ht : t ≤ 1) (k : ℕ) :
    (avram_redux19_original_strict_negative_marked_times_finite
      X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t) =
    (avram_redux19_original_strict_negative_marked_times_finite
      X ω t k).toFinset.filter (fun u => s < u) := by
  classical
  have hOne := avram_redux19_original_strict_negative_marked_times_finite
    X ω (1 : ℝ≥0) k
  have hT := avram_redux19_original_strict_negative_marked_times_finite X ω t k
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hu, ⟨hus, hut⟩⟩
    have hU := (hOne.mem_toFinset).mp hu
    refine ⟨(hT.mem_toFinset).mpr ⟨hU.1, hut, hU.2.2⟩, hus⟩
  · rintro ⟨hu, hus⟩
    have hU := (hT.mem_toFinset).mp hu
    refine ⟨(hOne.mem_toFinset).mpr ⟨hU.1, le_trans hU.2.1 ht, hU.2.2⟩, ⟨hus, hU.2.1⟩⟩
