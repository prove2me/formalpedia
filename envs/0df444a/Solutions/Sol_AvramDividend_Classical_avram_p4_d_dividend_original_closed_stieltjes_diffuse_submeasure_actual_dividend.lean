-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:05:11.490448+00:00
-- url     : https://prove2.me/submissions/894dee08-c634-4122-9b96-46aaee235668

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The diffuse component of any genuine additive original closed-horizon
Stieltjes decomposition is a submeasure of the actual dividend measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
      μatom + μdiffuse) :
    μdiffuse ≤ dividendMeasure D ω := by
  calc
    μdiffuse ≤ μatom + μdiffuse := by
      exact le_add_of_nonneg_left bot_le
    _ = (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) := hsplit.symm
    _ ≤ dividendMeasure D ω := Measure.restrict_le_self
