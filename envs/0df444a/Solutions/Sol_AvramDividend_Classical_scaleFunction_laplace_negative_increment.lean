-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_laplace_negative_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:57:56.099005+00:00
-- url     : https://prove2.me/submissions/392f4b70-5fd5-42c9-b094-6fc1d9e9ee51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
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
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * (W (x + y) - W x)) =
      (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ := by
  have hshift :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + y))
        (Ioi (0 : ℝ)) :=
    scaleFunction_shiftedLaplace_integrable X q W hW θ y hθ hqθ hy
  have hbase :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x)
        (Ioi (0 : ℝ)) :=
    (hW.2.2.2.2 θ hθ hqθ).1
  calc
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * (W (x + y) - W x)) =
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-(θ * x)) * W (x + y) -
            Real.exp (-(θ * x)) * W x) := by
              apply integral_congr_ae
              filter_upwards with x
              ring
    _ = (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) * W (x + y)) -
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) * W x) :=
            integral_sub hshift hbase
    _ = Real.exp (θ * y) * (X.ψ θ - q)⁻¹ -
          (X.ψ θ - q)⁻¹ := by
            rw [scaleFunction_shifted_laplace_transform X q W hW θ y hθ hqθ hy,
              (hW.2.2.2.2 θ hθ hqθ).2]
    _ = (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ := by ring
