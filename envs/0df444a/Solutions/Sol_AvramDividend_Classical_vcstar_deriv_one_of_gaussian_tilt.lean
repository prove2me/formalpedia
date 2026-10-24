-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_gaussian_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:32:03.906056+00:00
-- url     : https://prove2.me/submissions/7266d5bb-fd43-412a-a8d6-b549ca891e9e

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (hσ : 0 < X.σ)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_gaussian X hX q hq W hW hσ
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  have hpositive : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have hderivpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos_of_tilted_positive_monotone X hX q hq W hW
      hpositive hdiff htilt
  exact vcstar_deriv_one_of_local_scale_deriv_positive W ha
    (hdiff _ ha) (hderivpos _ ha)
