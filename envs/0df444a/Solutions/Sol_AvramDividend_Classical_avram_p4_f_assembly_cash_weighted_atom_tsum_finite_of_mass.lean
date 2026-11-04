-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_cash_weighted_atom_tsum_finite_of_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:25:43.180667+00:00
-- url     : https://prove2.me/submissions/20be0d8f-3c1a-44a6-bec0-b5aefa81d67a

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Subunit cash weights preserve finite total atomic mass. -/
theorem solution
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hf : ∀ a : A, f a.1 ≤ 1)
    (hmass : (∑' a : A, μatom {a.1}) ≠ ⊤) :
    (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤ := by
  have hterm : ∀ a : A, f a.1 * μatom {a.1} ≤
      μatom {a.1} := by
    intro a
    calc
      f a.1 * μatom {a.1} ≤
          1 * μatom {a.1} := by
        gcongr
        all_goals exact hf a
      _ = μatom {a.1} := one_mul _
  exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm)
    (lt_top_iff_ne_top.mpr hmass)).ne
