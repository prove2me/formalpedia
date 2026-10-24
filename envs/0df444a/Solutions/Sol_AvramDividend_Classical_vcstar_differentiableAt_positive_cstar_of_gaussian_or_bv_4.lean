-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:13:02.606491+00:00
-- url     : https://prove2.me/submissions/41136d40-176c-4694-87b5-a207d63d59df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    DifferentiableAt ℝ (vcstar W) (cstar W).toReal := by
  have hvder : deriv (vcstar W) (cstar W).toReal = 1 := by
    rcases hregular with hσ | hbv
    · obtain ⟨_, htilt⟩ :=
        scaleFunction_tilted_positive_monotone X hX q hq W hW
      exact vcstar_deriv_one_of_gaussian_tilt X hX q hq W hW
        hc hcpos hσ htilt
    · have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
        scaleFunction_contDiff_one X hX q hq W hW
      exact vcstar_deriv_one_of_bv_contDiff_one X hX q hq W hW
        hc hcpos hbv hreg
  have hvne : deriv (vcstar W) (cstar W).toReal ≠ 0 := by
    rw [hvder]
    exact one_ne_zero
  exact differentiableAt_of_deriv_ne_zero hvne
