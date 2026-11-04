-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_real_mesh_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:04:15.53605+00:00
-- url     : https://prove2.me/submissions/545f8621-b0ff-407a-80a7-5a5c5d81dd84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_uniform_negative_grid_probability_mass
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original negative source-event O(h) estimate bounds the uniform
grid probability mass for all sufficiently fine positive real meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (((n + 1 : ℕ) : ℝ≥0∞) *
        P {ω : Ω | X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω ≤ -ε}) ≤
      ENNReal.ofReal (C * (T : ℝ)) := by
  obtain ⟨C, hC, hBound⟩ :=
    avram_p2_original_uniform_negative_grid_probability_mass
      X ε hε (T : ℝ) (by positivity)
  refine ⟨C, hC, ?_⟩
  have hMesh := avram_p2_a_zero_rate_positive_uniform_mesh_tendsto T hT
  filter_upwards [hMesh.eventually hBound] with n hn
  apply hn (n + 1)
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  have hEq : (((n + 1 : ℕ) : ℝ) * ((T : ℝ) / ((n : ℝ) + 1))) = (T : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hd]
  exact hEq.le
