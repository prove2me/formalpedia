-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:10:39.544742+00:00
-- url     : https://prove2.me/submissions/02bf0718-4fe5-487b-8a8b-ebf0639b97b6

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For the actual BV Lévy path, its complete negative left-jump real series is
summable on each interval and agrees with the finite ENNReal total. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 =>
        (if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) ∧
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal =
        ∑' u : ℝ≥0,
          (if s < u ∧ u ≤ t then
            ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by
  filter_upwards [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV] with ω hω
  intro s t hst
  have hfin :
      (∑' u : ℝ≥0,
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0) ≠ ⊤ := ne_of_lt (hω s t hst)
  have hterms (u : ℝ≥0) :
      (if s < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0) ≠ ⊤ := by
    split_ifs
    · exact ne_of_lt ENNReal.ofReal_lt_top
    · simp
  exact ⟨ENNReal.summable_toReal hfin, ENNReal.tsum_toReal_eq hterms⟩
