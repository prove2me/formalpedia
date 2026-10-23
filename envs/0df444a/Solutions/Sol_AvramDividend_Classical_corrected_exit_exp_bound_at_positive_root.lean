-- Prove2me | solution 1 for AvramDividend.Classical.corrected_exit_exp_bound_at_positive_root
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:02:52.774353+00:00
-- url     : https://prove2.me/submissions/b286da33-e8ed-4498-9458-4018d3bc2c24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectationCorrected X q a x ≤
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by
  have hkilled :=
    corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing X q a x
  have hupper := levy_positive_root_unrestricted_upcrossing_discount_bound
    X q hq φ hφ hroot (a - x) (sub_nonneg.mpr hxa)
  exact hkilled.trans hupper
