-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_negative_uniform_grid_levy_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:42:07.255756+00:00
-- url     : https://prove2.me/submissions/1ba5af5d-5d62-4254-bce4-8659ee125ef2

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_negative_test_real_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- Uniform original increment tests converge in mean to the original negative Lévy rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    Tendsto (fun n : ℕ => ∫ ω,
      ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) *
        ∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ))))) := by
  exact avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
    P X T hT g hg hc
    (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ))))
    (avram_p2_j_ui_original_compact_negative_test_real_rate
      X g hg hc hneg)
