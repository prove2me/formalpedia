-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:14:37.756083+00:00
-- url     : https://prove2.me/submissions/e4ff7883-3215-4a98-945c-12472038ef40

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Cash measure's atom converts to its discounted real right jump. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (t : ℝ≥0) (μatom : Measure ℝ)
    (hμatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hdelta : 0 ≤ rightLimit D t ω - D t ω) :
    (ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      μatom {(t : ℝ)}).toReal =
      Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) := by
  rw [hμatom, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofReal hdelta,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
