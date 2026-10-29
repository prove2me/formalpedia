-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_standing_bv_derivative_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:39:34.684144+00:00
-- url     : https://prove2.me/submissions/bc5150fa-f5a2-4d88-81e7-5370f594b9e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Under the actual classical standing hypothesis, the bounded-variation
    scale derivative diverges because standing forces an absolutely continuous
    Lévy measure, hence positive-axis C¹ regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    Tendsto (deriv W) atTop atTop := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
      X hX q hq W hW hbv hac
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  exact bv_scaleDeriv_tendsto_atTop_of_C1 X hX q hq W hW hbv hdiff
