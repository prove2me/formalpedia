-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:00:09.176472+00:00
-- url     : https://prove2.me/submissions/30ca719a-bed1-483b-a653-83e622e2f8b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
    ((1 / 10 : ℝ≥0) : ℝ≥0∞) <
      ruinTime X 0 (barrierStrategy X 0 0) ω := by
  have hd : 0 ≤ X.drift := by rw [hDrift]; norm_num
  have hZero :=
    avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
      X ω 1 hd (by
        intro t ht
        rw [hPath t ht]
        ring)
  have hSafe : ∀ t : ℝ≥0, t < 1 →
      0 ≤ riskProcess X 0 (barrierStrategy X 0 0) t ω := by
    intro t ht
    rw [(hZero t (le_of_lt ht)).2]
  have hRuin :=
    avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
      X 0 (barrierStrategy X 0 0) ω (1 : ℝ≥0) hSafe
  have hTen : ((1 / 10 : ℝ≥0) : ℝ≥0∞) < (1 : ℝ≥0∞) := by
    norm_num
  exact lt_of_lt_of_le hTen hRuin
