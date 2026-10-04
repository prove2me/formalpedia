-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_jump_moment_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:39:37.175415+00:00
-- url     : https://prove2.me/submissions/565330e3-7946-4342-925c-ee13b27c41cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option autoImplicit false

universe u

open MeasureTheory Set
open scoped NNReal ENNReal

theorem c04fb14e_pointwise (y : ℝ) :
    ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ≤
      ENNReal.ofReal (min 1 (y ^ 2)) +
        (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y := by
  rw [Real.coe_toNNReal']
  rcases le_or_gt 0 y with hy | hy
  · have : max (-y) 0 = 0 := max_eq_right (by linarith)
    rw [this, min_eq_left (by norm_num : (0:ℝ) ≤ 1), ENNReal.ofReal_zero]
    exact bot_le
  · rcases le_or_gt y (-1) with hy1 | hy1
    · have h1 : min (max (-y) 0) 1 = 1 := by
        rw [max_eq_left (by linarith)]; exact min_eq_right (by linarith)
      have h2 : min 1 (y ^ 2) = 1 := min_eq_left (by nlinarith)
      rw [h1, h2]
      exact le_self_add
    · have hmem : y ∈ Ioo (-1 : ℝ) 0 := ⟨hy1, hy⟩
      rw [indicator_of_mem hmem]
      have h1 : min (max (-y) 0) 1 = |y| := by
        rw [max_eq_left (by linarith), min_eq_left (by linarith), abs_of_neg hy]
      rw [h1]
      exact le_add_self

open scoped NNReal ENNReal in open AvramDividend.Classical MeasureTheory Set in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1)
       ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) ≠ ⊤ := by
  have hmeas : Measurable (fun y : ℝ => Real.toNNReal (-y)) :=
    measurable_real_toNNReal.comp measurable_neg
  have hf : Measurable (fun z : ℝ≥0 => ENNReal.ofReal (min (z : ℝ) 1)) := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_coe_nnreal_real.min measurable_const
  rw [lintegral_map hf hmeas]
  apply ne_of_lt
  calc (∫⁻ y, ENNReal.ofReal (min ((Real.toNNReal (-y) : ℝ≥0) : ℝ) 1) ∂X.ν)
      ≤ ∫⁻ y, (ENNReal.ofReal (min 1 (y ^ 2)) +
          (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y) ∂X.ν :=
        lintegral_mono (fun y => c04fb14e_pointwise y)
    _ = (∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) +
          ∫⁻ y, (Ioo (-1 : ℝ) 0).indicator (fun y => ENNReal.ofReal |y|) y ∂X.ν := by
        apply lintegral_add_left
        exact ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id.pow_const 2))
    _ = (∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) +
          ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν := by
        rw [lintegral_indicator measurableSet_Ioo]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨X.ν_integrable, hbv.2⟩
