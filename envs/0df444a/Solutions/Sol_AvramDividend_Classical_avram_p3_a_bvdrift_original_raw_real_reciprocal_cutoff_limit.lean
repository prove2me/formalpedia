-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_reciprocal_cutoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:04:58.131149+00:00
-- url     : https://prove2.me/submissions/add27bf9-82cf-41b7-905a-51721f066525

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Cutoffs of actual BV negative-jump magnitudes converge monotonically
to the genuine real sum of signed source left jumps on each interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let M : ℝ≥0 → ℝ≥0∞ := fun u : ℝ≥0 =>
        if s < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0
      (⨆ n : ℕ, (∑' u : ℝ≥0,
        if (n : ℝ≥0∞)⁻¹ < M u then M u else 0).toReal) =
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total X hBV,
     avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hcut hraw
  intro s t hst
  have hlimit := hcut s t hst
  have hvalue := (hraw s t hst).2
  dsimp at hlimit
  exact hlimit.trans hvalue
