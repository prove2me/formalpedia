-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:30:03.761805+00:00
-- url     : https://prove2.me/submissions/8cba7cf6-add2-43c1-b0f9-7a54edc8fd77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_primitive_deriv_positive
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exact compensated source-generator increment on a strict small crossing jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hx0 : 0 < x) (hxr : x < r) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r) =
        r * W x - ∫ t in (0 : ℝ)..x, W t := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hzero : U (x - r) = 0 := by
    exact avram_wave4_p2_scale_primitive_zero_nonpositive
      X q W hW (x - r) (by linarith)
  have hd : deriv U x = W x :=
    scaleFunction_primitive_deriv_positive X q W hW x hx0
  have hy : -r < 0 := by linarith
  calc
    SpectrallyNegativeLevy.generatorIntegrand U x (-r) =
        U (x - (-(-r))) - U x +
          (if -(-r) < 1 then (-(-r)) * deriv U x else 0) :=
      (generatorIntegrand_negative_jump_reflection U x (-r) hy).symm
    _ = r * W x - U x := by
      simp only [neg_neg, if_pos hr1, hzero, hd, zero_sub, zero_add]
      ring
