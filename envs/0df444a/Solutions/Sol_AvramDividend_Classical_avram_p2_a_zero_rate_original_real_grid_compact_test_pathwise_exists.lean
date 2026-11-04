-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_real_grid_compact_test_pathwise_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:01.794572+00:00
-- url     : https://prove2.me/submissions/e4b26ee4-09d2-4272-8e9a-9204e2854dce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Every original Lévy sample has a genuine compact-test limit in the
real-to-NNReal mesh convention used by the independent expectation theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    ∀ ω : Ω, ∃ z : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (X.X (((i + 1 : ℕ) : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
            X.X ((i : ℝ≥0) *
              Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
        atTop (𝓝 z) := by
  intro ω
  obtain ⟨F, _, hlim⟩ :=
    avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
      X ω T hT ρ hρ f hf hvanish
  refine ⟨∑ t ∈ F, f (X.X t ω -
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t), ?_⟩
  simpa only [avram_p2_a_zero_rate_real_nnreal_uniform_step_coe] using hlim
