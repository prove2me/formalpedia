-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:43:40.970237+00:00
-- url     : https://prove2.me/submissions/5103c0d5-f2f1-43e9-a5af-3c6a04e8dd4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Under Standing, a genuine original stopped-minimum scale
harmonicity hypothesis yields the strict corrected two-sided exit
scale ratio for both variation branches and both endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
      ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x =
      ENNReal.ofReal (W x / W a) := by
  have hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    by_cases hBV : X.BoundedVariation
    · exact
        (avram_root29_03_bv_stopped_min_terminal_exit_factorisation
          X hX q hq W hW hBV a x ha hx0 hxa).symm.trans hKilled
    · exact
        (avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
          X hBV q hq W hW a x ha hxa).symm.trans hKilled
  exact chat04_exit_ratio_of_stopped_balance
    X hX q hq W hW a x ha hx0 hxa hBalance
