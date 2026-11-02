-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_large_jump_absolute_tsum_finite_each_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:18:22.109753+00:00
-- url     : https://prove2.me/submissions/887d546f-5933-4904-88db-69c015807ddb

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every actual source path has finite total absolute size of jumps separated
from zero on a compact horizon, including for unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    (∑' u : ℝ≥0,
      if 0 < u ∧ u ≤ T ∧
        δ ≤ dist (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0
      then ENNReal.ofReal |X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u|
      else 0) < ⊤ := by
  classical
  let mark : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ δ ≤ dist (mark u) 0}
  have hS : S.Finite := by
    exact avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω T δ hδ
  change (∑' u : ℝ≥0,
    if u ∈ S then ENNReal.ofReal |mark u| else 0) < ⊤
  have hEq : (∑' u : ℝ≥0,
      if u ∈ S then ENNReal.ofReal |mark u| else 0) =
      ∑ u ∈ hS.toFinset, (if u ∈ S then ENNReal.ofReal |mark u| else 0) := by
    apply tsum_eq_sum (s := hS.toFinset)
    intro u hu
    have hnot : u ∉ S := by
      intro hmem
      exact hu (hS.mem_toFinset.mpr hmem)
    simp [hnot]
  rw [hEq]
  apply (ENNReal.sum_lt_top).2
  intro u hu
  split_ifs <;> simp
