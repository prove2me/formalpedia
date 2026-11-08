-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:12:20.193912+00:00
-- url     : https://prove2.me/submissions/99d53e0a-b85c-401f-8c60-3ce0fd359e07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_strict_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_strict_loss_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Source-measurability of the product and loss separately implies their
almost-everywhere strong measurability for the original Levy law. -/
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
    AEStronglyMeasurable W P ∧ AEStronglyMeasurable L P := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hW : Measurable W := by
    simpa only [T, S, W, L] using
      (avram_bv_jump8_turn13_original_strict_product_measurable X hX hBV k n)
  have hL : Measurable L := by
    simpa only [T, S, W, L] using
      (avram_bv_jump8_turn13_original_strict_loss_measurable X hX hBV k n)
  change AEStronglyMeasurable W P ∧ AEStronglyMeasurable L P
  exact ⟨hW.aestronglyMeasurable, hL.aestronglyMeasurable⟩
