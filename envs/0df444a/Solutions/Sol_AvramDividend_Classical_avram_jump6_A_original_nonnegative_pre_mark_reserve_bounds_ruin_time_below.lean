-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:34:10.44749+00:00
-- url     : https://prove2.me/submissions/a6639843-f0a2-4eb2-b217-0d461d792f05

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0)
    (hPre : ∀ t : ℝ≥0, t < σ → 0 ≤ riskProcess X x D t ω) :
    (σ : ℝ≥0∞) ≤ ruinTime X x D ω := by
  unfold ruinTime
  refine le_iInf fun t => le_iInf fun ht => ?_
  have hnot : ¬ t < σ := by
    intro hlt
    exact (not_lt_of_ge (hPre t hlt)) ht
  exact_mod_cast (le_of_not_gt hnot)
