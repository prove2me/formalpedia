-- Prove2me | solution 1 for AvramDividend.Classical.esscher_preserves_infinite_small_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:53:42.875286+00:00
-- url     : https://prove2.me/submissions/7c2078f9-a470-4c37-8224-774dfbd79ab0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_small_jump_weight_lower
import Theorems.Thm_AvramDividend_Classical_positive_density_preserves_infinite_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂ν) = ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y|
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) = ⊤ := by
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  let f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (φ * y))
  let g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal |y|
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-φ))
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hmem : ∀ᵐ y : ℝ ∂ν.restrict S, y ∈ S :=
    ae_restrict_mem (μ := ν) measurableSet_Ioo
  have hbound : ∀ᵐ y : ℝ ∂ν.restrict S, c ≤ f y := by
    filter_upwards [hmem] with y hy
    exact esscher_small_jump_weight_lower φ y hφ hy.1.le
  have hvar' : (∫⁻ y : ℝ, g y ∂ν.restrict S) = ⊤ := by
    simpa only [S, g] using hvar
  have hmain :
      (∫⁻ y : ℝ, g y ∂((ν.withDensity f).restrict S)) = ⊤ := by
    rw [restrict_withDensity (μ := ν) measurableSet_Ioo f]
    exact positive_density_preserves_infinite_lintegral
      (ν.restrict S) f g hf hg c hc hbound hvar'
  simpa [S, f, g] using hmain
