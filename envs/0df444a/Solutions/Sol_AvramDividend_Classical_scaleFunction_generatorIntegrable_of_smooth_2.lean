-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:06:40.324142+00:00
-- url     : https://prove2.me/submissions/981bd806-d040-4b1c-8ceb-e2569e4b2b22

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Split the three smoothness alternatives and apply their verified
scale-function regularity and local jump-integrability estimates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by
  intro x hx
  rcases h_smooth with hσ | hbv | hC2
  · have hC2big : ContDiffOn ℝ 2 W (Ioi 0) :=
      scaleFunction_contDiffOn_two_of_sigma_pos X hX q hq W hW hσ
    have hC2 : ContDiffOn ℝ 2 W (Ioo 0 a) :=
      hC2big.mono (by
        intro y hy
        exact hy.1)
    exact scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW a x hx hC2
  · have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
    exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv x hx.1 hC1
  · exact scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW a x hx hC2
