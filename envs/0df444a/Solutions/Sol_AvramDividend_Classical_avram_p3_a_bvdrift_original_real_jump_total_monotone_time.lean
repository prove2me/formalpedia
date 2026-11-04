-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_real_jump_total_monotone_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:59:57.981021+00:00
-- url     : https://prove2.me/submissions/42eba5ab-237f-4d44-884f-208396aa7ab7

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

/-- The total actual source BV negative-jump magnitude is nondecreasing
in the genuine observation time, with its exact finite real value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV]
    with ω hω
  let J (u : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
  let total (t : ℝ≥0) : ℝ≥0∞ :=
    ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then J u else 0
  change Monotone (fun t => (total t).toReal)
  intro s t hst
  have hfin : total t ≠ ⊤ :=
    ne_of_lt (hω 0 t (show (0 : ℝ≥0) ≤ t from zero_le))
  have hle : total s ≤ total t := by
    apply ENNReal.tsum_le_tsum
    intro u
    by_cases hu : 0 < u ∧ u ≤ s
    · have hut : u ≤ t := hu.2.trans hst
      have htu : 0 < u ∧ u ≤ t := ⟨hu.1, hut⟩
      simp [hu, htu]
    · simp [hu]
  exact ENNReal.toReal_mono hfin hle
