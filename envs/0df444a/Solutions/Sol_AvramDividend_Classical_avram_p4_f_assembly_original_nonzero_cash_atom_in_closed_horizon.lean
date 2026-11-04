-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:50:49.771687+00:00
-- url     : https://prove2.me/submissions/b7984a4e-d942-491b-a75c-17fbfee37d5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonzero source atomic dividend must lie in the true closed stopped interval. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (A : Set ℝ) (a : A)
    (hnonzero : μatom {a.1} ≠ 0) :
    0 ≤ a.1 ∧ a.1 ≤ (T : ℝ) := by
  have ha : a.1 ∈ Icc (0 : ℝ) (T : ℝ) := by
    by_contra hnot
    exact hnonzero (avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
      D ω T μatom μdiffuse hsplit a.1 hnot)
  exact ha
