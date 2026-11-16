-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_unit_drift_zero_barrier_exact_linear_dividends
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:39:19.213401+00:00
-- url     : https://prove2.me/submissions/a11fb943-60e2-4391-9bd3-58cfb94160d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = (t : ℝ) * X.drift) :
    ∀ t : ℝ≥0, t ≤ T →
      barrierStrategy X 0 0 t ω = (t : ℝ) ∧
      riskProcess X 0 (barrierStrategy X 0 0) t ω = 0 := by
  have hn : 0 ≤ X.drift := by rw [hDrift]; norm_num
  have hZero :=
    avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
      X ω T hn (by
        intro t ht
        rw [hPath t ht]
        ring)
  intro t ht
  obtain ⟨hD, hR⟩ := hZero t ht
  rw [hDrift] at hD
  exact ⟨by simpa using hD, hR⟩
