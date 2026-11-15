-- Prove2me | solution 1 for AvramDividend.Classical.avram_a32_original_finiteactivity_physical_jumpfree_residual_cadlag_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:54:37.953074+00:00
-- url     : https://prove2.me/submissions/91f68439-7f01-45d8-85e6-4819ed8c2695

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Removing actual finite-activity jumps from the original source leaves a right-continuous, left-limited jumpfree residual on each horizon. -/
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
        (∀ t : ℝ≥0,
          ContinuousWithinAt
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
            (Ici t) t) ∧
        (∀ t : ℝ≥0, 0 < t →
          Tendsto
            (fun v => f v - ∑ u ∈ S, if u ≤ v then j u else 0)
            (𝓝[<] t)
            (𝓝 (Function.leftLim f t -
              ∑ u ∈ S, if u < t then j u else 0))) ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ T →
          f t - (∑ u ∈ S, if u ≤ t then j u else 0) =
          Function.leftLim f t -
            (∑ u ∈ S, if u < t then j u else 0)) := by
  classical
  filter_upwards [
    avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
      X hFinite] with ω hω
  intro T
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
  obtain ⟨S, hS, hJRight, hJLeft, hDelta⟩ := hω T
  have hFLeft (t : ℝ≥0) (ht : 0 < t) :
      Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) := by
    obtain ⟨l, hl⟩ := X.leftLim ω t ht
    exact tendsto_leftLim_of_tendsto ⟨l, hl⟩
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro t
    exact (X.rightCont ω t).sub (hJRight t)
  · intro t ht
    exact (hFLeft t ht).sub (hJLeft t ht)
  · intro t ht htT
    have hJ := hDelta t ht htT
    dsimp [j] at hJ
    linarith
