-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_restricted_cash_atom_eq_rightjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:14:33.135604+00:00
-- url     : https://prove2.me/submissions/08c75928-9f93-4da1-9984-01b6a04b8298

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original restricted dividend-measure singletons are source right jumps. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T t : ℝ≥0) (ht : t ≤ T)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hdiff : NullSingletonClass μdiffuse)
    (hatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω)) :
    ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω) := by
  letI : NullSingletonClass μdiffuse := hdiff
  simpa [hsplit] using hatom
