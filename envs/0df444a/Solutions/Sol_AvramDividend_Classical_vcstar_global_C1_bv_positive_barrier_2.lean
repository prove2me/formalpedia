-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_global_C1_bv_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:07:49.390603+00:00
-- url     : https://prove2.me/submissions/eed6355d-4fe5-482d-a909-82c5266a94bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_C1_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- BV C1 gluing reduces exactly to positive-axis stochastic W regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  obtain ⟨hpositive, htilt⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  have hderivpos : ∀ x : ℝ, 0 < x → 0 < deriv W x :=
    scaleDeriv_pos_of_tilted_positive_monotone
      X hX q hq W hW hpositive hdiff htilt
  have hderivcont : ContinuousOn (deriv (vcstar W)) (Ioi (0 : ℝ)) :=
    vcstar_deriv_continuous_C1_positive W ha hreg
      (hderivpos _ ha)
  have hgrad := vcstar_deriv_ge_one_of_scale_C1_tilt
    X hX q hq W hW hreg htilt
  have hdOn : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (hgrad x hx).1.differentiableWithinAt
  exact contDiffOn_one_of_differentiable_continuous_deriv_Ioi
    (vcstar W) hdOn hderivcont
