-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrable_scaleFunction_of_contDiffOn_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:43:40.180979+00:00
-- url     : https://prove2.me/submissions/a853740d-08c9-4c29-a996-1a9e8e0a338f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The compensated Lévy generator jump integral of the scale function converges
at every point of `(0, a)` when the scale function is twice continuously
differentiable there.

This is the universally quantified form of the Proved theorem
`scaleFunction_generatorIntegrable_of_contDiff_two` (`a977868a`), which states
the same conclusion at a single point `x ∈ (0, a)`.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by
  intro x hx
  obtain ⟨C, hC, hbound⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
      X q W hW a x hx hC2
  apply generatorIntegrable_of_min_sq_bound X W x C hC
  · exact scaleFunction_generatorIntegrand_aestronglyMeasurable X q W hW x
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (μ := X.ν) measurableSet_Iio] with y hy
    exact hbound y hy
