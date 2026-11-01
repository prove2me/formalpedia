-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:51:05.591386+00:00
-- url     : https://prove2.me/submissions/96c6ed26-155d-4d7f-bce6-60f8edf92b48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_C2_jump_continuity
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_continuousAt_of_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Local continuity of the original Lévy generator residual for a monotone smooth test function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (hcont : Continuous f)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator f x - q * f x) (Icc l u) := by
  have hderiv : ContinuousOn (deriv f) (Ioo 0 a) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hae : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand f z y)
          (Icc l u) x := by
    intro x hx
    have hxa : x ∈ Ioo (0 : ℝ) a :=
      ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
    have hD : ContinuousAt (deriv f) x :=
      hderiv.continuousAt (isOpen_Ioo.mem_nhds hxa)
    filter_upwards [] with y
    exact (generatorIntegrand_continuousAt_of_continuous
      f x y hcont.continuousAt hcont.continuousAt hD).continuousWithinAt
  exact generator_residual_continuousOn_compact_of_C2_jump_continuity
    X q f a l u hl hlu hu hC2
    (avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_C2
      X f hnonneg hmono a l u hl hlu hu hC2 hae)
