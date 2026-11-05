-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep9_original_BV_uniform_small_unmarked_grid_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:54:14.863197+00:00
-- url     : https://prove2.me/submissions/8e262a36-360f-4cd9-8ffc-5f566f8389de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ marked : Finset ℝ≥0,
        ∀ (u : ℕ → ℝ≥0) (cells : Finset ℕ),
          StrictMono u →
          (∀ i ∈ cells, u (i + 1) ≤ T) →
          (∀ i ∈ cells, ∀ t ∈ marked,
            ¬ (u i < t ∧ t ≤ u (i + 1))) →
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0
          Finset.sum cells (fun i => J (u (i + 1)) - J (u i)) < ε := by
  filter_upwards
    [avram_p3_f_chainlimit_original_BV_finite_negative_times_tail X hBV T,
     avram_integration_sweep8_original_BV_uniform_pathwise_grid_jump_mass_tail X hBV T]
      with ω hsmall hgrid
  intro ε hε
  obtain ⟨marked, hInside, htail⟩ := hsmall ε hε
  refine ⟨marked, ?_⟩
  intro u cells hu hBound hAvoid
  let j : ℝ≥0 → ℝ := fun t =>
    if 0 < t ∧ t ≤ T then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω else 0
  have hj : ∀ t : ℝ≥0, 0 ≤ j t := by
    intro t
    dsimp [j]
    split_ifs with ht
    · exact (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
        X ω t ht.1).1
    · exact le_refl 0
  have hRewrite :
      (∑' t : ℝ≥0, if t ∈ marked then 0 else j t) =
      (∑' t : ℝ≥0, if t ∈ marked then 0 else |j t|) := by
    apply tsum_congr
    intro t
    by_cases ht : t ∈ marked
    · simp [ht]
    · simp [ht, abs_of_nonneg (hj t)]
  have hTailSmall :
      (∑' t : ℝ≥0, if t ∈ marked then 0 else |j t|) < ε := by
    simpa only [j] using htail
  have hUniform := hgrid u cells marked hu hBound hAvoid
  calc
    Finset.sum cells (fun i =>
      (∑' s : ℝ≥0, if 0 < s ∧ s ≤ u (i + 1) then
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0) -
      (∑' s : ℝ≥0, if 0 < s ∧ s ≤ u i then
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω else 0)) ≤
      (∑' t : ℝ≥0, if t ∈ marked then 0 else j t) := hUniform
    _ = (∑' t : ℝ≥0, if t ∈ marked then 0 else |j t|) := hRewrite
    _ < ε := hTailSmall
