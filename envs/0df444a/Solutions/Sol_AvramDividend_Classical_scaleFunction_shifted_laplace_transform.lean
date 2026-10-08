-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_shifted_laplace_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:39:00.899831+00:00
-- url     : https://prove2.me/submissions/42571a81-8bdf-42d0-b2f5-c1072efb35ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_shift_real
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_Ioi_of_zero_negative

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
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) =
      Real.exp (θ * y) * (X.ψ θ - q)⁻¹ := by
  have hshiftneg : ∀ z : ℝ, z < 0 → W (z + y) = 0 := by
    intro z hz
    exact hW.1 (z + y) (by linarith)
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) =
        ∫ x : ℝ, Real.exp (-(θ * x)) * W (x + y) := by
          symm
          exact weightedLaplace_integral_Ioi_of_zero_negative
            (fun z => W (z + y)) θ hshiftneg
    _ = Real.exp (θ * y) *
          (∫ x : ℝ, Real.exp (-(θ * x)) * W x) :=
            weightedLaplace_integral_shift_real W θ y
    _ = Real.exp (θ * y) *
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) := by
            rw [weightedLaplace_integral_Ioi_of_zero_negative W θ hW.1]
    _ = Real.exp (θ * y) * (X.ψ θ - q)⁻¹ := by
          rw [(hW.2.2.2.2 θ hθ hqθ).2]
