-- Prove2me | solution 1 for AvramDividend.Classical.avram_a31_original_physical_finiteactivity_nested_horizon_jump_consistency_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:49:14.986728+00:00
-- url     : https://prove2.me/submissions/62b6a1f3-f460-47bf-b815-790f44261e25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a31_physical_jump_accumulator_horizon_consistency_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original physical negative-jump accumulators on nested horizons have identical causal history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T U : ℝ≥0, T ≤ U →
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S R : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ u, u ∈ R ↔ 0 < u ∧ u ≤ U ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) =
          (∑ u ∈ R, if u ≤ t then j u else 0)) := by
  classical
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  intro T U hTU
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Finset ℝ≥0 := (hω T).toFinset
  let R : Finset ℝ≥0 := (hω U).toFinset
  have hS (u : ℝ≥0) : u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0 :=
    (hω T).mem_toFinset
  have hR (u : ℝ≥0) : u ∈ R ↔ 0 < u ∧ u ≤ U ∧ j u ≠ 0 :=
    (hω U).mem_toFinset
  exact ⟨S, R, hS, hR,
    avram_a31_physical_jump_accumulator_horizon_consistency_20261114
      j T U hTU S R hS hR⟩
