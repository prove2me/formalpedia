-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn13_original_equalcell_product_expectation_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:33:32.157144+00:00
-- url     : https://prove2.me/submissions/826887cc-b68f-420d-af43-84e8fba64043

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_coord8_t10_indep_equalcell_power
import Theorems.Thm_AvramDividend_Classical_avram_coord8_t10_equalcell_marked_product_iIndep
import Theorems.Thm_AvramDividend_Classical_avram_coord8_t10_equalcell_marked_product_stationary_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The finite-product expectation follows from exact cell independence and stationarity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    (∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P) =
      (∫ ω : Ω, ∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^ (n + 1) := by
  dsimp only
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change (∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P) =
    (∫ ω : Ω, ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^ (n + 1)
  have hind := avram_coord8_t10_equalcell_marked_product_iIndep X hX hBV k n
  have hsame := avram_coord8_t10_equalcell_marked_product_stationary_mean X hX hBV k n
  exact avram_coord8_t10_indep_equalcell_power P n C
    (fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    hind.1 hind.2 hsame
