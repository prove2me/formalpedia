-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:53:39.781664+00:00
-- url     : https://prove2.me/submissions/8170f252-9d4b-48f9-bdc8-c726feda3fa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_positive_probability_nojump_linear_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution (T : ℝ≥0) :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift)} := by
  obtain ⟨P, 𝓕, X, hs, hbv, hν, hfinite, hd, hσ⟩ :=
    avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
  have hPositive :=
    avram_bvb_obstruction_original_positive_probability_nojump_linear_source
      X hs hbv (ne_of_lt hfinite) T
  refine ⟨P, 𝓕, X, hs, hbv, hν, hfinite, hd, hσ, ?_⟩
  simpa only [Set.mem_setOf_eq] using hPositive
