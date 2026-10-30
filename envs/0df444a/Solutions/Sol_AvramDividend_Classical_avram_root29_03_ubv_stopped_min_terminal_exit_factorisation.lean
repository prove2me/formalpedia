-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:18:08.876021+00:00
-- url     : https://prove2.me/submissions/579c1000-742e-4091-89ba-9f311c491973

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- For the genuine unbounded-variation Lévy process, the q-scale
reward stopped at the finite first two-sided exit factors as the
strict upper-exit discounted mass times the barrier scale.
This is a terminal-payoff conversion, not killed harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
  exact
    (avram_root29_03_exact_qscale_two_branch_terminal_conversion
      X q W hW a x ha hxa).trans
    (chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
      X hnbv q hq W hW a x hxa)
