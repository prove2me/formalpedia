-- Prove2me | solution 2 for AvramDividend.Classical.corrected_exit_exp_bound_at_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:51:27.367365+00:00
-- url     : https://prove2.me/submissions/bd3e17d3-1655-4d82-b822-edebeb3cca87

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
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
  calc
    twoSidedExitExpectationCorrected X q a x ≤
        ∫⁻ ω, if twoSidedExitUpTimeCorrected X (a - x) ω < (⊤ : ℝ≥0∞)
          then ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (twoSidedExitUpTimeCorrected X (a - x) ω))))
          else 0 ∂P := by
            exact
              AvramDividend.Classical.corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
                X q a x
    _ ≤ ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by
      exact AvramDividend.Classical.levy_positive_root_unrestricted_upcrossing_discount_bound
        X q hq φ hφ hroot (a - x) (sub_nonneg.mpr hxa)
