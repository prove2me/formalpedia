-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_raw_J_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:39:02.938843+00:00
-- url     : https://prove2.me/submissions/7086be76-ec4e-44d1-9a27-28b0303a7c81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) ≤
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
      X hBV] with ω hω
  intro s t hst
  have hsplit := hω s t hst
  have hnonneg :=
    avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
      X ω s t hst
  linarith only [hsplit, hnonneg]
