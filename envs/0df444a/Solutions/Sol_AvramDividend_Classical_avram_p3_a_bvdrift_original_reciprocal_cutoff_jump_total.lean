-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_reciprocal_cutoff_jump_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:45:33.9632+00:00
-- url     : https://prove2.me/submissions/2f4434d1-0128-4053-bf34-6c40122c98d1

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete original negative left-jump magnitude total is the monotone
supremum over positive reciprocal size cutoffs on the actual source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0
    (⨆ n : ℕ, ∑' v : ℝ≥0,
      if (n : ℝ≥0∞)⁻¹ < M v then M v else 0) =
      ∑' v : ℝ≥0, M v := by
  exact avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full
    (fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0)