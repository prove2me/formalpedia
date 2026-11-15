-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:46.76288+00:00
-- url     : https://prove2.me/submissions/1659829d-8737-4880-8004-9cd291378c42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_right_continuous_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_left_limit_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every finite-activity physical source path has a finite cadlag jump accumulator with exactly the original jumps on each compact horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ t : ℝ≥0,
          ContinuousWithinAt
            (fun v : ℝ≥0 => ∑ u ∈ S, if u ≤ v then j u else 0)
            (Ici t) t) ∧
        (∀ t : ℝ≥0, 0 < t →
          Tendsto
            (fun v : ℝ≥0 => ∑ u ∈ S, if u ≤ v then j u else 0)
            (𝓝[<] t)
            (𝓝 (∑ u ∈ S, if u < t then j u else 0))) ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ T →
          (∑ u ∈ S, if u ≤ t then j u else 0) -
          (∑ u ∈ S, if u < t then j u else 0) = j t) := by
  classical
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  intro T
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Finset ℝ≥0 := (hω T).toFinset
  have hS (u : ℝ≥0) : u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0 :=
    (hω T).mem_toFinset
  have hRegular (A : Finset ℝ≥0) :
      (∀ t : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => ∑ u ∈ A, if u ≤ v then j u else 0)
          (Ici t) t) ∧
      (∀ t : ℝ≥0, 0 < t →
        Tendsto
          (fun v : ℝ≥0 => ∑ u ∈ A, if u ≤ v then j u else 0)
          (𝓝[<] t)
          (𝓝 (∑ u ∈ A, if u < t then j u else 0))) := by
    classical
    induction A using Finset.induction_on with
    | empty =>
      constructor
      · intro t
        simpa using (continuousWithinAt_const :
          ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Ici t) t)
      · intro t _
        simpa using (tendsto_const_nhds :
          Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[<] t) (𝓝 0))
    | @insert u A hu ih =>
      constructor
      · intro t
        have hs :=
          avram_a30_single_mark_causal_step_right_continuous_20261114
            u (j u) t
        have hSum : ContinuousWithinAt
            (fun v : ℝ≥0 => (if u ≤ v then j u else 0) +
              (∑ w ∈ A, if w ≤ v then j w else 0)) (Ici t) t := by
          convert hs.add (ih.1 t) using 1
          funext v
          rfl
        simpa only [Finset.sum_insert hu] using hSum
      · intro t ht
        have hs :=
          avram_a30_single_mark_causal_step_left_limit_20261114
            u (j u) t ht
        simpa [Finset.sum_insert hu] using hs.add (ih.2 t ht)
  obtain ⟨hRight, hLeft⟩ := hRegular S
  refine ⟨S, hS, hRight, hLeft, ?_⟩
  intro t ht htT
  rw [avram_a30_finite_marked_jump_accumulator_exact_left_jump_20261114
    S j t]
  change (if t ∈ S then j t else 0) = j t
  by_cases hj : j t = 0
  · have hNot : t ∉ S := by
      intro hMem
      exact ((hS t).mp hMem).2.2 hj
    simp [hNot, hj]
  · have hMem : t ∈ S := (hS t).mpr ⟨ht, htT, hj⟩
    simp [hMem]
