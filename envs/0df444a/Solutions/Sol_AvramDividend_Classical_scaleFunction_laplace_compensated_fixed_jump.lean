-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_laplace_compensated_fixed_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:12:17.0269+00:00
-- url     : https://prove2.me/submissions/54920c0a-4309-465c-861a-3197e100c282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_negative_increment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable

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
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hder : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ -
        (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) *
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv W x) := by
  let k : ℝ :=
    y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
  have hshift :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + y))
        (Ioi (0 : ℝ)) :=
    scaleFunction_shiftedLaplace_integrable X q W hW θ y hθ hqθ hy
  have hbase :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x)
        (Ioi (0 : ℝ)) :=
    (hW.2.2.2.2 θ hθ hqθ).1
  have hinc :
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) * (W (x + y) - W x)) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun x : ℝ => Real.exp (-(θ * x)) * (W (x + y) - W x)) =
        (fun x : ℝ =>
          Real.exp (-(θ * x)) * W (x + y) -
            Real.exp (-(θ * x)) * W x) := by
      funext x
      ring
    rw [hfun]
    exact hshift.sub hbase
  have hcomp : IntegrableOn (fun x : ℝ =>
      k * (Real.exp (-(θ * x)) * deriv W x)) (Ioi (0 : ℝ)) :=
    hder.const_mul k
  have hrewrite :
      (∫ x in Ioi (0 : ℝ),
         Real.exp (-(θ * x)) *
           SpectrallyNegativeLevy.generatorIntegrand W x y) =
      ∫ x in Ioi (0 : ℝ),
        (Real.exp (-(θ * x)) * (W (x + y) - W x)) -
          k * (Real.exp (-(θ * x)) * deriv W x) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [k, SpectrallyNegativeLevy.generatorIntegrand]
    simp only [Pi.one_def]
    ring
  rw [hrewrite, integral_sub hinc hcomp, integral_const_mul]
  rw [scaleFunction_laplace_negative_increment X q W hW θ y hθ hqθ hy]
