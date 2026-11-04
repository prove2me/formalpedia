-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:44:45.694964+00:00
-- url     : https://prove2.me/submissions/fffa2944-ed89-4a16-9828-85011564cef5

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Finite source atomic ENNReal total implies exact real tsum conversion. -/
theorem solution
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∑' a : A, f a.1 * μatom {a.1}).toReal =
        ∑' a : A, (f a.1 * μatom {a.1}).toReal := by
  have hpoint : ∀ a : A, f a.1 * μatom {a.1} ≠ ⊤ := by
    intro a
    have hle : f a.1 * μatom {a.1} ≤
        (∑' b : A, f b.1 * μatom {b.1}) := by
      exact ENNReal.le_tsum a
    exact (lt_of_le_of_lt hle
      (lt_top_iff_ne_top.mpr hfinite)).ne
  exact avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
    A μatom f hfinite hpoint
