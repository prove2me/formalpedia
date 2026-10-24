-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_differentiableAt_positive_cstar_of_gaussian_or_bv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:12:38.223044+00:00
-- url     : https://prove2.me/submissions/7a3cabae-8600-4bad-9fa4-4e434deabc13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive

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
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have hWdiff : DifferentiableAt ℝ W (cstar W).toReal :=
    (hreg.differentiableOn_one _ ha).differentiableAt
      (Ioi_mem_nhds ha)
  have hdpos : 0 < deriv W (cstar W).toReal :=
    scaleDeriv_pos X hX q hq W hW _ ha
  have hvder : deriv (vcstar W) (cstar W).toReal = 1 :=
    vcstar_deriv_one_of_local_scale_deriv_positive W ha hWdiff hdpos
  have hvne : deriv (vcstar W) (cstar W).toReal ≠ 0 := by
    rw [hvder]
    exact one_ne_zero
  exact differentiableAt_of_deriv_ne_zero hvne
