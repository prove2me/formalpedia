-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_bv_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T09:31:50.216147+00:00
-- url     : https://prove2.me/submissions/8cb8f248-4f02-4b33-be0c-60adfbd20a9f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
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
    (hbv : X.BoundedVariation)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  obtain ⟨hpositive, htilt⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hderivpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos_of_tilted_positive_monotone X hX q hq W hW
      hpositive hdiff htilt
  exact vcstar_deriv_one_of_local_scale_deriv_positive W ha
    (hdiff _ ha) (hderivpos _ ha)
