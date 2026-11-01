-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:55:56.957998+00:00
-- url     : https://prove2.me/submissions/24427b02-4cf4-4acf-8e52-8c235f5268ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_primitive_deriv_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- Positive-axis second derivative of the primitive is exactly W'. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 2 (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x =
      deriv W x := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hlocal : deriv U =ᶠ[nhds x] W := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact scaleFunction_primitive_deriv_positive X q W hW y hy
  have heq : deriv (deriv U) x = deriv W x := hlocal.deriv_eq
  simpa [U, iteratedDeriv_succ] using heq
