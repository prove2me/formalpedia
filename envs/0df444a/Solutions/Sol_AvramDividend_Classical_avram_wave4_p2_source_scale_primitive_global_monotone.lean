-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_global_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:57:38.080126+00:00
-- url     : https://prove2.me/submissions/a1c6ea17-421d-4b14-9816-a9008ef8d4c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The genuine source q-scale interval primitive is globally nondecreasing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Monotone (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hUzero (z : ℝ) (hz : z ≤ 0) : U z = 0 :=
    avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz
  have hUnonneg (z : ℝ) (hz : 0 ≤ z) : 0 ≤ U z := by
    change 0 ≤ ∫ t in (0 : ℝ)..z, W t
    exact intervalIntegral.integral_nonneg hz (fun t ht => hW.2.1 t ht.1)
  change Monotone U
  intro a b hab
  by_cases hb : b ≤ 0
  · rw [hUzero a (hab.trans hb), hUzero b hb]
  · have hb0 : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
    by_cases ha : a ≤ 0
    · rw [hUzero a ha]
      exact hUnonneg b hb0
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
