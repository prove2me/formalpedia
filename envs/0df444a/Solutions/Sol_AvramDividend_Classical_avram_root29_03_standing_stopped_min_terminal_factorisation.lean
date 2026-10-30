-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_standing_stopped_min_terminal_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:45:23.332189+00:00
-- url     : https://prove2.me/submissions/a0ab28a3-21ce-4bc4-bd68-b8043a13d247

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- In every variation branch under Standing, the original finite
minimum-exit discounted q-scale terminal reward factors through
the strict discounted upper-before-ruin expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
  by_cases hBV : X.BoundedVariation
  · exact avram_root29_03_bv_stopped_min_terminal_exit_factorisation
      X hX q hq W hW hBV a x ha hx0 hxa
  · exact avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
      X hBV q hq W hW a x ha hxa
