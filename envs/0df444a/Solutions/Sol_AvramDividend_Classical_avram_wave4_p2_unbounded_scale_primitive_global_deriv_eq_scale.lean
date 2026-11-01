-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:34:44.632841+00:00
-- url     : https://prove2.me/submissions/14a33627-12a6-453c-a5cc-b09c4eeb36ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_primitive_deriv_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- Actual unbounded-variation primitive is globally differentiable with U' = W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    deriv (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) = W := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  funext x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hEv : U =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW y (le_of_lt hy)
    have hD : deriv U x = 0 := by
      rw [hEv.deriv_eq]
      simp
    rw [hD, hW.1 x hx]
  · subst x
    have hzero : W 0 = 0 :=
      chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
    exact (avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
      X hnbv q hq W hW).2.trans hzero.symm
  · exact scaleFunction_primitive_deriv_positive X q W hW x hx
