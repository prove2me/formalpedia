-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_prod_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:37:11.416021+00:00
-- url     : https://prove2.me/submissions/c51487b0-15af-47c5-a454-2e49ecfd75e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_weighted_global_fubini_of_prod_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ)))
    (hzero : W 0 = 0)
    (horigin : (X.σ ^ 2 / 2) * deriv W 0 = 1)
    (hkernel : IntegrableOn (fun y : ℝ =>
       Real.exp (θ * y) - 1 -
         θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
       (Iio 0) X.ν)
    (hGint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         ((X.σ ^ 2 / 2) * deriv (deriv W) x + X.c * deriv W x))
       (Ioi (0 : ℝ)))
    (hJint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) *
         (∫ y in Iio (0 : ℝ),
           SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν))
       (Ioi (0 : ℝ)))
    (hprod : Integrable
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (X.generator W x - q * W x)) = 0 := by
  have hfubini :=
    scaleFunction_generator_weighted_global_fubini_of_prod_integrable
      X W θ hprod
  exact scaleFunction_generator_residual_weightedLaplace_zero_gaussian_of_fubini
    X q W hW θ hθ hqθ hcont hderiv hcont1 hderiv1 hDint hD2int
    hzero horigin hkernel hGint hJint hfubini
