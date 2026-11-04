-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_cash_atom_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:41:06.379735+00:00
-- url     : https://prove2.me/submissions/33e8c68c-93cd-4b81-916e-70cb0226321c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Finite source restricted Cash measure controls every countable atomic mass. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hfinite : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ ≠ ⊤) :
    (∑' a : A, μatom {a.1}) ≠ ⊤ := by
  rw [avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
    μatom A hA]
  have hle : μatom A ≤
      ((dividendMeasure D ω).restrict
        (Icc (0 : ℝ) (T : ℝ))) Set.univ := by
    calc
      μatom A ≤ μatom Set.univ :=
        measure_mono (Set.subset_univ _)
      _ ≤ _ := by rw [hsplit]; simp
  exact (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfinite)).ne
