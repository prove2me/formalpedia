-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:26:36.775339+00:00
-- url     : https://prove2.me/submissions/c833d6f6-2626-4412-a6f6-92cca441a8c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original restricted Cash atomic component vanishes outside its horizon. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (s : ℝ) (hs : s ∉ Icc (0 : ℝ) (T : ℝ)) :
    μatom {s} = 0 := by
  have hi : ({s} : Set ℝ) ∩ Icc (0 : ℝ) (T : ℝ) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hz⟩
    exact hs hz
  have hzero : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) {s} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton s), hi]
    exact measure_empty
  rw [hsplit, Measure.add_apply] at hzero
  exact (add_eq_zero.mp hzero).1
