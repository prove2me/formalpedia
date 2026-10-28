-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_log_concave_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:53:04.47046+00:00
-- url     : https://prove2.me/submissions/8733a57c-d106-409e-a285-a3150525fe02

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_log_concave_of_differentiable
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hlogdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun z : ℝ => Real.log (W z)) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (W z)) := by
  have hpos := AvramDividend.Classical.scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  refine AvramDividend.Classical.positive_ratio_order_log_concave_of_differentiable W hpos
    hlogdiff ?_
  intro x y t hx hxy ht
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hm := AvramDividend.Classical.corrected_exit_shifted_initial_reserve_monotone X q t x y hxy
  rw [hExit (t + x) x (by linarith) hx (by linarith),
    hExit (t + y) y (by linarith) hy (by linarith),
    ENNReal.ofReal_le_ofReal_iff (div_nonneg (hpos y hy).le (hpos _ (by linarith)).le)] at hm
  rwa [add_comm x t, add_comm y t]
