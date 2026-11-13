-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_frozen_source_counter_rep_of_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:18:10.138475+00:00
-- url     : https://prove2.me/submissions/fcd79e83-3809-4b93-b5b7-9ed7a64cc014

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Real original-path marked counts factor through a measurable frozen-prefix functional. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧ ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by
  classical
  obtain ⟨F, hMeas, hCount⟩ :=
    avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
      T B hB
  refine ⟨F, hMeas, ?_⟩
  intro ω
  let Y : ℝ≥0 → ℝ := fun v => X.X (min v T) ω
  have hJumpEq (u : ℝ≥0) (hu : 0 < u) (huT : u ≤ T) :
      Y u - Function.leftLim Y u =
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
    dsimp [Y]
    rw [min_eq_left huT,
      avram_wave7_06_original_frozen_prefix_leftLim_before_stop X ω T u hu huT]
  have hSet :
      {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B} =
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ B} := by
    ext u
    constructor
    · rintro ⟨hu, _, huT, hj, hm⟩
      have heq := hJumpEq u hu huT
      exact ⟨hu, huT, by simpa only [heq] using hj,
        by simpa only [heq] using hm⟩
    · rintro ⟨hu, huT, hj, hm⟩
      have heq := hJumpEq u hu huT
      exact ⟨hu, hu, huT, by simpa only [heq] using hj,
        by simpa only [heq] using hm⟩
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) =
      ({u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard :=
      avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω 0 T B hB
    _ = ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ B}).encard := by rw [hSet]
    _ = F Y := hCount Y (hCad ω).1 (hCad ω).2
