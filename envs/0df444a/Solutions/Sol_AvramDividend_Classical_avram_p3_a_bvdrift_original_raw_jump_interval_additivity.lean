-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_interval_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:23:21.6092+00:00
-- url     : https://prove2.me/submissions/57765f3a-d4ca-4880-9c82-5623d61ed729

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Summable raw actual negative source left jumps split exactly under
every ordered subdivision of a BV sample-path interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
      (∑' u : ℝ≥0, if s < u ∧ u ≤ r then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) =
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) + (∑' u : ℝ≥0, if t < u ∧ u ≤ r then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity X hBV,
     avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV,
     avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum X hBV]
    with ω hadd hraw hreal
  intro s t r hst htr
  have hsplit := hadd s t r hst htr
  have hsr := (hraw s r (hst.trans htr)).2
  have hleft := (hraw s t hst).2
  have hright := (hraw t r htr).2
  have hconvr := (hreal s r (hst.trans htr)).2
  have hconvl := (hreal s t hst).2
  have hconvrt := (hreal t r htr).2
  rw [← hconvr, ← hconvl, ← hconvrt] at hsplit
  rw [hsr, hleft, hright] at hsplit
  exact hsplit
