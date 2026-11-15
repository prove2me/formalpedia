-- Prove2me | solution 1 for AvramDividend.Classical.avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:03:56.749206+00:00
-- url     : https://prove2.me/submissions/d0202056-05f5-417e-8971-4318d68a9e68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a33_cadlag_zero_left_jumps_continuous_to_horizon_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let f : ℝ≥0 → ℝ := fun t => X.X t ω
      let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
      ∃ S : Finset ℝ≥0,
        (∀ t, t ∈ S ↔ 0 < t ∧ t ≤ T ∧ j t ≠ 0) ∧
        (∀ t : ℝ≥0, t ≤ T →
          ContinuousAt
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0) t) := by
  classical
  filter_upwards [
    avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
      X hFinite] with ω hω
  intro T
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
  obtain ⟨S, hS, hRight, hLeft, hZero⟩ := hω T
  refine ⟨S, hS, ?_⟩
  have hL (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) :
      Tendsto
        (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
        (𝓝[<] t)
        (𝓝 (f t - ∑ u ∈ S, if u ≤ t then j u else 0)) := by
    rw [hZero t ht htT]
    exact hLeft t ht
  exact avram_a33_cadlag_zero_left_jumps_continuous_to_horizon_20261114
    (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
    T hRight hL
