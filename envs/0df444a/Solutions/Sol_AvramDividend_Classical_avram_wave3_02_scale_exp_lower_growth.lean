-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_scale_exp_lower_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:46:03.721002+00:00
-- url     : https://prove2.me/submissions/24ba8d2e-6b15-4397-a93c-734c3d88f9d8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine q-scale function grows at least exponentially past reserve
one under the positive Esscher exponent, without assuming global C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ a : ℝ, 1 ≤ a →
      W 1 * Real.exp (φ * (a - 1)) ≤ W a := by
  obtain ⟨φ, hφ, hratio⟩ :=
    avram_wave3_02_esscher_ratio_exp_bound X hX q hq W hW
  obtain ⟨hWpos, _⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  refine ⟨φ, hφ, ?_⟩
  intro a ha
  have hWa : 0 < W a := hWpos a (by linarith)
  have hr : W 1 / W a ≤ Real.exp (-φ * (a - 1)) :=
    hratio 1 a (by norm_num) ha
  have hb : W 1 ≤ Real.exp (-φ * (a - 1)) * W a :=
    (div_le_iff₀ hWa).1 hr
  have hm := mul_le_mul_of_nonneg_left hb
    (le_of_lt (Real.exp_pos (φ * (a - 1))))
  calc
    W 1 * Real.exp (φ * (a - 1)) =
      Real.exp (φ * (a - 1)) * W 1 := mul_comm _ _
    _ ≤ Real.exp (φ * (a - 1)) *
        (Real.exp (-φ * (a - 1)) * W a) := hm
    _ = W a := by
      rw [← mul_assoc, ← Real.exp_add]
      have heq : φ * (a - 1) + -φ * (a - 1) = 0 := by ring
      rw [heq, Real.exp_zero, one_mul]
