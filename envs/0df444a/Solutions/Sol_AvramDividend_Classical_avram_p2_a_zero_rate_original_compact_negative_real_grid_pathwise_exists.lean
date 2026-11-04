-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_real_grid_pathwise_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:57:21.013129+00:00
-- url     : https://prove2.me/submissions/acb5c332-b71f-417b-929e-44c0a14a198b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Original Lévy compact negative test grid sums possess real-mesh pathwise limits without auxiliary separation data. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∀ ω : Ω, ∃ z : ℝ,
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (𝓝 z) := by
  obtain ⟨ρ, hρ, hvanish⟩ :=
    avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
      g hg hc hneg
  intro ω
  obtain ⟨F, _, hlim⟩ :=
    avram_p2_a_zero_rate_original_source_uniform_grid_compact_test_jump_limit
      X ω T hT ρ hρ g hg hvanish
  refine ⟨∑ t ∈ F, g (X.X t ω -
    Function.leftLim (fun u : ℝ≥0 => X.X u ω) t), ?_⟩
  simpa only [avram_p2_a_zero_rate_real_nnreal_uniform_step_coe] using hlim
