-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB55_original_barrier_ruinTime_ge_tube_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:36:14.279867+00:00
-- url     : https://prove2.me/submissions/646ef4da-8efc-4af7-af3e-cb3fd6398086

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- An original barrier reserve above the positive cutoff cannot ruin before T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ)) :
    (T : ℝ≥0∞) ≤
      ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω := by
  unfold ruinTime
  refine le_iInf fun t => le_iInf fun hneg => ?_
  by_contra hfail
  have ht : t ≤ T := by
    have hlt : (t : ℝ≥0∞) < (T : ℝ≥0∞) := lt_of_not_ge hfail
    exact_mod_cast (le_of_lt hlt)
  have hB :=
    avram_gbB38_barrier_reserve_above_cutoff_on_tube X t ω
      (fun s hs => hTube s (hs.trans ht))
  have hp : (0 : ℝ) <
      riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω := by
    linarith
  linarith
