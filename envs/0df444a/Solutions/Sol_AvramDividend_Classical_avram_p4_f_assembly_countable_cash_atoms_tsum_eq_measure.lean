-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:15:11.748858+00:00
-- url     : https://prove2.me/submissions/8f4ee189-51ae-4276-a7ed-dd9c14538dff

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The countable source Cash atom masses sum exactly to the mass of A. -/
theorem solution
    (μatom : Measure ℝ) (A : Set ℝ) (hA : A.Countable) :
    (∑' a : A, μatom {a.1}) = μatom A := by
  simpa using
    (MeasureTheory.tsum_measure_preimage_singleton
      (μ := μatom) (s := A) hA
      (f := id) (by
        intro y hy
        simpa using (measurableSet_singleton y)))
