-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:43:35.192201+00:00
-- url     : https://prove2.me/submissions/718b5860-b231-4aa0-a296-829343f48568

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Safe source paths have no ruin strictly before their last certified safe time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (ε : ℝ≥0)
    (hSafe : ∀ t : ℝ≥0, t < ε → 0 ≤ riskProcess X x D t ω) :
    (ε : ℝ≥0∞) ≤ ruinTime X x D ω := by
  unfold ruinTime
  refine le_iInf (fun t => ?_)
  refine le_iInf (fun ht => ?_)
  have hge : ε ≤ t := le_of_not_gt (by
    intro hlt
    exact (not_lt_of_ge (hSafe t hlt)) ht)
  exact_mod_cast hge
