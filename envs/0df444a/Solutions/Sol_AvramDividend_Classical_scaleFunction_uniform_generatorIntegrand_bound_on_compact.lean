-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_uniform_generatorIntegrand_bound_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:36:22.320272+00:00
-- url     : https://prove2.me/submissions/4071ae9f-c17d-4103-85d7-3703b5edeffd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_near_zero_bound_on_compact
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_far_jump_bound_on_compact

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
    (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨r, Cnear, hr, hrle, hCnear, hnear⟩ :=
    scaleFunction_uniform_near_zero_bound_on_compact
      X q W hW a l u hl hlu hu hC2
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    scaleFunction_uniform_far_jump_bound_on_compact
      X q W hW a l u r hl hlu hu hr hC2
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
