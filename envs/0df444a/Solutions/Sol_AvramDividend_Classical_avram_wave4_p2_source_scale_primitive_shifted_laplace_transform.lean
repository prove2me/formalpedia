-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:04:20.961113+00:00
-- url     : https://prove2.me/submissions/ef622faa-177a-4688-ae5b-3846ac6b6f9b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_shift_real
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_Ioi_of_zero_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exact negative-shift Laplace transform of the actual scale primitive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ t in (0 : ℝ)..(x + y), W t)) =
      Real.exp (θ * y) * ((X.ψ θ - q)⁻¹ / θ) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hUzero (z : ℝ) (hz : z < 0) : U z = 0 :=
    avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z (le_of_lt hz)
  have hshiftneg : ∀ z : ℝ, z < 0 → U (z + y) = 0 := by
    intro z hz
    exact hUzero (z + y) (by linarith)
  have hWlap := hW.2.2.2.2 θ hθ.le hqθ
  have hUlap := positive_laplace_interval_primitive_real W θ hθ hWlap.1
  change (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * U (x + y)) = _
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * U (x + y)) =
        ∫ x : ℝ, Real.exp (-(θ * x)) * U (x + y) := by
      symm
      exact weightedLaplace_integral_Ioi_of_zero_negative
        (fun z => U (z + y)) θ hshiftneg
    _ = Real.exp (θ * y) *
          (∫ x : ℝ, Real.exp (-(θ * x)) * U x) :=
      weightedLaplace_integral_shift_real U θ y
    _ = Real.exp (θ * y) *
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * U x) := by
      rw [weightedLaplace_integral_Ioi_of_zero_negative U θ hUzero]
    _ = Real.exp (θ * y) * ((X.ψ θ - q)⁻¹ / θ) := by
      rw [hUlap.2, hWlap.2]
