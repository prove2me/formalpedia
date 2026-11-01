-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:48:20.350455+00:00
-- url     : https://prove2.me/submissions/59305b67-c7e6-4d38-9578-c41b4d0b07d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generator_weighted_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The actual primitive compensated jump kernel is jointly Borel measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) :
    Measurable
      (fun p : ℝ × ℝ => Real.exp (-θ * p.1) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2|) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hUzero (z : ℝ) (hz : z ≤ 0) : U z = 0 :=
    avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz
  have hUnonneg (z : ℝ) (hz : 0 ≤ z) : 0 ≤ U z := by
    change 0 ≤ ∫ t in (0 : ℝ)..z, W t
    exact intervalIntegral.integral_nonneg hz (fun t ht => hW.2.1 t ht.1)
  have hUmono : Monotone U := by
    intro a b hab
    by_cases hb : b ≤ 0
    · rw [hUzero a (hab.trans hb), hUzero b hb]
    · have hb0 : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
      by_cases ha : a ≤ 0
      · rw [hUzero a ha]; exact hUnonneg b hb0
      · have ha0 : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
        have hi : IntervalIntegrable W volume (0 : ℝ) b :=
          scaleFunction_intervalIntegrable_nonnegative X q W hW 0 b (le_refl 0) hb0
        have hWnn : ∀ z : ℝ, 0 ≤ W z := by
          intro z
          by_cases hz : 0 ≤ z
          · exact hW.2.1 z hz
          · rw [hW.1 z (lt_of_not_ge hz)]
        have hae : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) b)), 0 ≤ W z :=
          Filter.Eventually.of_forall hWnn
        exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ha0 hab hae hi
  have hUmeas : Measurable U := hUmono.measurable
  have hderU : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale X hnbv q hq W hW
  have hWmeas : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hderUmeas : Measurable (deriv U) := by
    rw [hderU]
    exact hWmeas
  change Measurable (fun p : ℝ × ℝ => Real.exp (-θ * p.1) *
    |SpectrallyNegativeLevy.generatorIntegrand U p.1 p.2|)
  exact avram_wave4_05_source_generator_weighted_kernel_joint_measurable
    U hUmeas hderUmeas θ
