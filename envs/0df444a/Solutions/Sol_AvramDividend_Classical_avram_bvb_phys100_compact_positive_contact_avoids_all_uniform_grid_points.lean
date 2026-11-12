-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:41:41.098484+00:00
-- url     : https://prove2.me/submissions/306609ab-578b-4d7a-a67d-26571a36d01d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys99_countable_uniform_grid_samples_are_null

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Positive-Lebesgue-mass compact contact sets exist in the unit horizon
while missing every point of an arbitrary countable family of grids. -/
theorem solution (u : ℕ → ℕ → ℝ) :
    let G : Set ℝ := Set.range (fun p : ℕ × ℕ => u p.1 p.2)
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧
      Disjoint K G ∧ 0 < (volume : Measure ℝ) K := by
  dsimp
  obtain ⟨hGmeas, hGnull⟩ :=
    AvramDividend.Classical.avram_bvb_phys99_countable_uniform_grid_samples_are_null u
  have hvol : (volume : Measure ℝ) (Icc (0 : ℝ) 1) = 1 := by
    norm_num [Real.volume_Icc]
  have hfinite : (volume : Measure ℝ) (Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [hvol]
    norm_num
  have hpositive : 0 < (volume : Measure ℝ) (Icc (0 : ℝ) 1) := by
    rw [hvol]
    norm_num
  exact AvramDividend.Classical.avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
    (volume : Measure ℝ) (Icc (0 : ℝ) 1)
    (Set.range (fun p : ℕ × ℕ => u p.1 p.2))
    measurableSet_Icc hGmeas hGnull hfinite hpositive
