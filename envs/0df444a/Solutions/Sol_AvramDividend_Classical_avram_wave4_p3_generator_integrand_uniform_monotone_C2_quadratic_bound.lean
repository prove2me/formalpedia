-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_monotone_C2_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:43:37.125483+00:00
-- url     : https://prove2.me/submissions/4d05c3b4-c0a5-40db-a43d-046e614aeaed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_far_monotone_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform integrable Lévy-kernel envelope on compact positive starting reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨r, Cnear, hr, hrle, hCnear, hnear⟩ :=
    avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
      X f a l u hl hlu hu hC2
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
      X f hnonneg hmono a l u r hl hlu hu hr hC2
  refine ⟨max Cnear Cfar, hCnear.trans (le_max_left _ _), ?_⟩
  intro x hx y hy
  by_cases hyFar : y ≤ -r
  · have h := hfar x hx y hy hyFar
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_max_right Cnear Cfar) (by positivity : 0 ≤ min 1 (y ^ 2)))
  · have hyNear : y ∈ Ioo (-r) 0 := ⟨lt_of_not_ge hyFar, hy⟩
    have hr1 : r ≤ 1 := hrle.trans (min_le_right l 1)
    have hyLower : (-1 : ℝ) < y := by linarith
    have hySquare : y ^ 2 < 1 := by
      have hpos : 0 < (1 + y) * (1 - y) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right hySquare.le
    rw [hmin]
    exact (hnear x hx y hyNear).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cnear Cfar) (sq_nonneg y))
