-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_global_C1_bv_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:24:43.933925+00:00
-- url     : https://prove2.me/submissions/9511d403-c8c5-4a64-b9cb-efb69e846706
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_on_positive_bv
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_differentiable_continuous_deriv_Ioi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
  have hdiff : DifferentiableOn ℝ (vcstar W) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxDiff := (vcstar_deriv_ge_one X hX q hq W hW x hx0).1
    exact hxDiff.differentiableWithinAt
  have hcont :
      ContinuousOn (deriv (vcstar W)) (Ioi 0) :=
    vcstar_deriv_continuous_on_positive_bv X hX q hq W hW hc hcpos hbv
  exact contDiffOn_one_of_differentiable_continuous_deriv_Ioi
    (vcstar W) hdiff hcont
