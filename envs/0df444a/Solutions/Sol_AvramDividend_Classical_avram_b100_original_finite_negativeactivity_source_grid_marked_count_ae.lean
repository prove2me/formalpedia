-- Prove2me | solution 1 for AvramDividend.Classical.avram_b100_original_finite_negativeactivity_source_grid_marked_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:07.467669+00:00
-- url     : https://prove2.me/submissions/cfe7269d-4979-4f51-b4ca-ee1c47c93948

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite original activity supplies actual source jump-time witnesses bounding every occupied physical cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0,
          u ∈ F ↔ 0 < u ∧ u ≤ T ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        (∀ J : Finset ℕ,
          (∀ i ∈ J, ∃ u ∈ F,
            u ∈ Ioc (grid i) (grid (i + 1))) →
          J.card ≤ F.card) := by
  classical
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  let F : Finset ℝ≥0 := (hω T).toFinset
  have hMem (u : ℝ≥0) :
      u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  refine ⟨F, hMem, ?_⟩
  intro J hJ
  let g : ℕ → ℝ≥0 := fun i =>
    if hi : i ∈ J then Classical.choose (hJ i hi) else 0
  have hG (i : ℕ) (hi : i ∈ J) :
      g i ∈ F ∧ g i ∈ Ioc (grid i) (grid (i + 1)) := by
    simpa only [g, dif_pos hi] using
      (Classical.choose_spec (hJ i hi))
  have hMap : Set.MapsTo g (J : Set ℕ) (F : Set ℝ≥0) := by
    intro i hi
    exact (hG i hi).1
  have hInj : Set.InjOn g (J : Set ℕ) := by
    intro i hi j hj heq
    have hLeft := (hG i hi).2
    have hRight : g i ∈ Ioc (grid j) (grid (j + 1)) := by
      simpa only [heq] using (hG j hj).2
    exact avram_wave7_06_monotone_marked_grid_index_unique
      grid hmono (g i) i j hLeft hRight
  exact Finset.card_le_card_of_injOn g hMap hInj
