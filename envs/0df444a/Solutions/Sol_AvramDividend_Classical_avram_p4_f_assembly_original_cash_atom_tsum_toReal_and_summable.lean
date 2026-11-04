-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:14:41.509857+00:00
-- url     : https://prove2.me/submissions/6b673d31-2b9b-4478-af90-8bcfba8609ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Finite source Cash atomic masses have a convergent real tsum. -/
theorem solution
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤)
    (hpoint : ∀ a : A, f a.1 * μatom {a.1} ≠ ⊤) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∑' a : A, f a.1 * μatom {a.1}).toReal =
        ∑' a : A, (f a.1 * μatom {a.1}).toReal := by
  exact ⟨ENNReal.summable_toReal hfinite, ENNReal.tsum_toReal_eq hpoint⟩
