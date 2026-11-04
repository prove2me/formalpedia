-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:34:39.375533+00:00
-- url     : https://prove2.me/submissions/4c7a0821-fb62-4237-8671-adbfa3ccb21e

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine bounded-variation source left-jump magnitude series is the
supremum of real-valued reciprocal cutoff totals on every ordered interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 =>
        if s < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0
      (⨆ n : ℕ, (∑' v : ℝ≥0,
        if (n : ℝ≥0∞)⁻¹ < M v then M v else 0).toReal) =
        (∑' v : ℝ≥0, M v).toReal := by
  filter_upwards [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV] with ω hω
  intro s t hst
  dsimp
  exact avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
    (fun v : ℝ≥0 =>
      if s < v ∧ v ≤ t then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0)
    (hω s t hst)
