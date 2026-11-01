-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_total_source_jump_magnitudes_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:42:46.674458+00:00
-- url     : https://prove2.me/submissions/9f14143c-8bc9-49eb-8bcb-b9606dab28c6

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual X hBV]
    with ω hbudget
  intro T
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have hvalid :
      ∀ u ∈ S.filter (fun v : ℝ≥0 => 0 < v ∧ v ≤ T),
        0 < u ∧ u ≤ T := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  have hbound := hbudget T
    (S.filter (fun v : ℝ≥0 => 0 < v ∧ v ≤ T)) hvalid
  simpa only [Finset.sum_filter] using hbound
