-- Prove2me | solution 4 for AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T04:59:10.562181+00:00
-- url     : https://prove2.me/submissions/e61b0823-4fbd-4744-a496-14f129d799f4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_harmonicity_general_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hfac :=
    chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
      X hnbv q hq W hW a x hxa
  have hhar :=
    chat04_unbounded_stopped_scale_harmonicity_general_reserve
      X hnbv q hq W hW a x hxa
  rw [← hfac]
  exact hhar
