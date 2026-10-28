-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_uniform_linear_jump_bound_on_compact_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:50:00.617848+00:00
-- url     : https://prove2.me/submissions/6d64b733-589f-412f-a955-238304841888

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Join uniform C1 near and far jump estimates into a BV integrable envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y| := by
  obtain ⟨r, Cnear, hr, hr1, _, hCnear, hnear⟩ :=
    scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
      X q W hW a l u hl hlu hu hC1
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
      X q W hW a l u r hl hlu hu hr hC1
  let C : ℝ := max Cnear Cfar
  have hC : 0 ≤ C := le_trans hCnear (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hy0 : y < 0 := hy
  by_cases hsmall : -r < y
  · have hynear : y ∈ Ioo (-r) 0 := ⟨hsmall, hy0⟩
    have hyabs : |y| < 1 := by
      rw [abs_of_neg hy0]
      linarith
    have hmin : min (1 : ℝ) |y| = |y| := min_eq_right hyabs.le
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖
          ≤ Cnear * |y| := hnear x hx y hynear
      _ ≤ C * |y| :=
          mul_le_mul_of_nonneg_right (le_max_left Cnear Cfar) (abs_nonneg y)
      _ = C * min 1 |y| := by rw [hmin]
  · have hyr : y ≤ -r := le_of_not_gt hsmall
    have hmn : 0 ≤ min (1 : ℝ) |y| :=
      le_min zero_le_one (abs_nonneg y)
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖
          ≤ Cfar * min 1 |y| := hfar x hx y hy0 hyr
      _ ≤ C * min 1 |y| :=
          mul_le_mul_of_nonneg_right (le_max_right Cnear Cfar) hmn
