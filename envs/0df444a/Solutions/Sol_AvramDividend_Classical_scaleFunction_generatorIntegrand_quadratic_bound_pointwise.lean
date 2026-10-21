-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_bound_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:12:09.504956+00:00
-- url     : https://prove2.me/submissions/12c237cd-8bf9-41a9-a7c5-54c278129f56

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
The generator integrand of the scale function is bounded by a constant times
`min 1 (y ^ 2)` at every negative point.

This is the Proved theorem
`scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two` (`4cd125e2`),
with the bound stated for `y ∈ Iio 0` and with `|·|` in place of `‖·‖`; in a
real normed space the two agree.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
      X q W hW a x hx hC2
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hy0 : y < 0 := Set.mem_Iio.mp hy
  simpa only [Real.norm_eq_abs] using hbound y hy0
