-- Prove2me | solution 1 for AvramDividend.Classical.avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:49:02.759106+00:00
-- url     : https://prove2.me/submissions/4e33b7f6-c6bd-462a-beb7-9ab0b7a62de8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original finite-activity actual jump accumulation is nonpositive at each time on a common conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) ≤ 0) := by
  classical
  filter_upwards [
    avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
      X hFinite] with ω hω
  intro T
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  obtain ⟨S, hS, _, _, _⟩ := hω T
  refine ⟨S, hS, ?_⟩
  intro t ht
  apply Finset.sum_nonpos
  intro u hu
  by_cases hut : u ≤ t
  · simp only [if_pos hut]
    exact avram_a65_original_physical_negative_jump_mark_nonpositive_allpaths_20261114
      X ω u ((hS u).mp hu).1
  · simp [hut]
