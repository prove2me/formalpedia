-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_jump8_turn13_original_equalcell_product_expectation_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:44:37.931195+00:00
-- url     : https://prove2.me/submissions/576c29f2-a823-4d9a-8b28-e6e079d44acf

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
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
  classical
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let F : Ω → ℝ := fun ω =>
    ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change (∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P) =
    (∫ ω : Ω, F ω ∂P) ^ (n + 1)
  have hIndep : iIndepFun C P ∧ ∀ i, AEStronglyMeasurable (C i) P :=
    avram_coord8_t10_equalcell_marked_product_iIndep X hX hBV k n
  have hSame : ∀ i : Fin (n + 1),
      (∫ ω, C i ω ∂P) = ∫ ω, F ω ∂P :=
    avram_coord8_t10_equalcell_marked_product_stationary_mean X hX hBV k n
  exact avram_coord8_t10_indep_equalcell_power P n C F
    hIndep.1 hIndep.2 hSame
