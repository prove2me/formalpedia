-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:41:42.472903+00:00
-- url     : https://prove2.me/submissions/ba6293b5-cc62-4afb-a74d-72a9d546071e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Every strict prefix of an original narrow-barrier source tube lies before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ)) :
    ∀ s : ℝ≥0, s < T →
      (s : ℝ≥0∞) <
        ruinTime X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω := by
  intro s hs
  exact lt_of_lt_of_le (by exact_mod_cast hs)
    (avram_gbB55_original_barrier_ruinTime_ge_tube_horizon X T ω hTube)
