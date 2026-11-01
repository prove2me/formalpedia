-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:30:10.93+00:00
-- url     : https://prove2.me/submissions/1e13b723-59ae-4d1c-9c5b-6e4673c60648

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_crossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Actual source compensated generator crossing section has weighted O(r²) mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioo (0 : ℝ) r) volume ∧
    (∫ x in Ioo (0 : ℝ) r,
      Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      W 1 * r^2 := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let s : Set ℝ := Ioo 0 r
  let f : ℝ → ℝ := fun x => Real.exp (-(θ*x)) *
    |SpectrallyNegativeLevy.generatorIntegrand U x (-r)|
  let g : ℝ → ℝ := fun x => Real.exp (-(θ*x)) *
    |r*W x-U x|
  have hWstr :=
    avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
      X q W hW r θ hr0 (le_of_lt hr1) hθ
  have heq : EqOn f g s := by
    intro x hx
    change Real.exp (-(θ*x)) *
      |SpectrallyNegativeLevy.generatorIntegrand U x (-r)| =
      Real.exp (-(θ*x)) * |r*W x-U x|
    rw [avram_wave4_p2_scale_primitive_generatorIntegrand_crossing
      X q W hW r x hr0 hr1 hx.1 hx.2]
  constructor
  · exact (integrableOn_congr_fun heq measurableSet_Ioo).2 hWstr.1
  · calc
      (∫ x in s, f x) = ∫ x in s, g x :=
        setIntegral_congr_fun measurableSet_Ioo heq
      _ ≤ W 1 * r^2 := hWstr.2
