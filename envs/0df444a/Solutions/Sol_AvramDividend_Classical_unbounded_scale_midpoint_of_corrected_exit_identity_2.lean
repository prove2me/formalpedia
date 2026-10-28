-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_scale_midpoint_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:35:29.102672+00:00
-- url     : https://prove2.me/submissions/d1286e5c-5bac-4705-bced-d7cf9df07633

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_midpoint_multiplicative_of_ratio_order
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Corrected exit identities and reserve comparison force midpoint log-concavity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x y : ℝ, 0 < x → x < y →
      W x * W y ≤ (W ((x + y) / 2)) ^ 2 := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  apply positive_midpoint_multiplicative_of_ratio_order W hpos
  intro x y t hx hxy ht
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxt : 0 < x + t := by linarith
  have hyt : 0 < y + t := by linarith
  have hxle : x ≤ x + t := by linarith
  have hyle : y ≤ y + t := by linarith
  have hmono :
      twoSidedExitExpectationCorrected X q (x + t) x ≤
      twoSidedExitExpectationCorrected X q (y + t) y := by
    simpa [add_comm] using
      (corrected_exit_shifted_initial_reserve_monotone X q t x y hxy)
  rw [hExit (x + t) x hxt hx hxle,
      hExit (y + t) y hyt hy hyle] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff
    (le_of_lt (div_pos (hpos y hy) (hpos (y + t) hyt)))).mp hmono
