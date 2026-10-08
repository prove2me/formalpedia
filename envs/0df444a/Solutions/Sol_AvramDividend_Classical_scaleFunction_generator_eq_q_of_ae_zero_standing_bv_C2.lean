-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:00:59.946715+00:00
-- url     : https://prove2.me/submissions/ceafce73-39c9-4270-8e7f-b7559a518ea1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_continuousOn_of_continuousOn_each_compact_Icc
import Theorems.Thm_AvramDividend_Classical_continuousOn_zero_of_ae_zero_restrict_Ioo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a) := by
    apply continuousOn_of_continuousOn_each_compact_Icc
    intro l u hl hlu hu
    exact generator_residual_continuousOn_compact_of_standing_bv_C2 X hX hbv q W hW a l u hl hlu hu hC2
  exact continuousOn_zero_of_ae_zero_restrict_Ioo
    (fun x : ℝ => X.generator W x - q * W x) a hcont hae
