-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:28:30.072159+00:00
-- url     : https://prove2.me/submissions/a10fe2bf-ca60-4bef-bfd1-526a87cfc644

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- An explicitly assumed original killed stopped-minimum q-scale
harmonicity identity implies the strict two-sided exit scale ratio.
The killed stochastic premise remains a visible hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
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
        ENNReal.ofReal (W x) :=
    (avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
      X hnbv q hq W hW a x ha hxa).symm.trans hKilled
  calc
    twoSidedExitExpectation X q a x =
      twoSidedExitExpectationCorrected X q a x :=
        chat04_twoSidedExitExpectation_eq_corrected X q a x
    _ = ENNReal.ofReal (W x / W a) :=
      chat01_unbounded_corrected_exit_ratio_of_stopped_balance
        X q hq W hW hnbv a x ha hx0 hxa hBalance
