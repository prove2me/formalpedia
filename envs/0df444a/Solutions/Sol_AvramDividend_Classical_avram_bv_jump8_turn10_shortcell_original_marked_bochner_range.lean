-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:32:02.317573+00:00
-- url     : https://prove2.me/submissions/cf17a0dc-fcd9-44ca-859d-e4b6a37dc0f2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_integrability
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Separate original marked-product integrability from elementary finite-product
range, then integrate the pointwise inequalities on the source probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Integrable W P ∧ Integrable L P ∧
    0 ≤ ∫ ω, W ω ∂P ∧ (∫ ω, W ω ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hint : Integrable W P ∧ Integrable L P := by
    simpa only [T, S, W, L] using
      (avram_bv_jump8_turn11_original_shortcell_integrability X hX hBV k n)
  have hbound : ∀ ω : Ω, 0 ≤ W ω ∧ W ω ≤ 1 := by
    simpa only [T, S, W] using
      (avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds X hX hBV k n)
  refine ⟨hint.1, hint.2, ?_, ?_⟩
  · exact integral_nonneg (fun ω => (hbound ω).1)
  · calc
      (∫ ω, W ω ∂P) ≤ (∫ _ : Ω, (1 : ℝ) ∂P) := by
        exact integral_mono hint.1 (integrable_const _) (fun ω => (hbound ω).2)
      _ = 1 := by simp
