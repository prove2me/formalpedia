-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:52:33.932192+00:00
-- url     : https://prove2.me/submissions/2a1eb5ff-85d9-41ea-a84b-65ed693654e9

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
    (σ : ℝ≥0) (hneg : riskProcess X x D σ ω < 0) :
    ruinTime X x D ω ≤ (σ : ℝ≥0∞) := by
  unfold ruinTime
  exact le_trans (iInf_le _ σ) (iInf_le _ hneg)
