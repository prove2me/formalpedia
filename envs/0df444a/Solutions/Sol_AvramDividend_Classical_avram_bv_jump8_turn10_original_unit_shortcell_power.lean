-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_original_unit_shortcell_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:40:42.538527+00:00
-- url     : https://prove2.me/submissions/4704402f-5958-493b-99c5-23d33bb11828

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_unit_partition_product
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_equalcell_product_expectation_power

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Split the actual original marked unit-time product into disjoint equal
cells, then apply stationary independent original increment laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P) = (∫ ω : Ω, ∏ u ∈
        (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^ (n + 1) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  have hPartition (ω : Ω) :
      (∏ u ∈ J ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
        ∏ i : Fin (n + 1), C i ω := by
    simpa only [T, J, C] using
      (avram_bv_jump8_turn13_original_unit_partition_product X hX hBV k n ω)
  have hIndep : (∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P) =
      (∫ ω : Ω, ∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^
          (n + 1) := by
    simpa only [T, J, S, C] using
      (avram_bv_jump8_turn13_original_equalcell_product_expectation_power
        X hX hBV k n)
  change (∫ ω : Ω, ∏ u ∈ J ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) =
    (∫ ω : Ω, ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^
        (n + 1)
  calc
    (∫ ω : Ω, ∏ u ∈ J ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) =
        ∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hPartition
    _ = _ := hIndep
