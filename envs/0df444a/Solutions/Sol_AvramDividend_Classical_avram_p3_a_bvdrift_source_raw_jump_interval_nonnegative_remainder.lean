-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:40.008636+00:00
-- url     : https://prove2.me/submissions/6ef58e66-97c9-4853-90de-67fc53072b3d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine BV raw signed real left-jump series, rather than merely its
nonnegative ENNReal encoding, enters the canonical drift increment with a
nonnegative residual on every original sample-path interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' (u : ℝ≥0),
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder X hBV,
     avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hωbudget hωraw
  intro s t hst
  obtain ⟨r, hr, hbudget⟩ := hωbudget s t hst
  have hconvert := (hωraw s t hst).2
  refine ⟨r, hr, ?_⟩
  rw [hconvert] at hbudget
  exact hbudget
