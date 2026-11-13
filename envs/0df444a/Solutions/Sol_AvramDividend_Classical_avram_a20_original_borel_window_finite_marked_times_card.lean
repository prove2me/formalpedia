-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_window_finite_marked_times_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:51:33.301511+00:00
-- url     : https://prove2.me/submissions/c9013a43-330e-419b-9b88-f4d6893c2111

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (hS : ({u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).Finite) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    (((hS.toFinset.filter
      (fun u : ℝ≥0 => s < u ∧ u ≤ t)).card : ℕ) : ℝ≥0∞) := by
  classical
  let S : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  let C : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ s < u ∧ u ≤ t ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  have hSub : C ⊆ S := by
    intro u hu
    exact ⟨hu.1, (hu.2.2.1).trans htT, hu.2.2.2.1, hu.2.2.2.2⟩
  have hFin : C.Finite := hS.subset hSub
  have hFilter : hFin.toFinset =
      hS.toFinset.filter (fun u : ℝ≥0 => s < u ∧ u ≤ t) := by
    ext u
    simp only [hFin.mem_toFinset, Finset.mem_filter,
      hS.mem_toFinset, C, S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hu0, hus, hut, hj, hb⟩
      exact ⟨⟨hu0, hut.trans htT, hj, hb⟩, hus, hut⟩
    · rintro ⟨⟨hu0, _, hj, hb⟩, hus, hut⟩
      exact ⟨hu0, hus, hut, hj, hb⟩
  have hN :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = (C.encard : ℝ≥0∞) := by
    simpa only [C] using
      (avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω s t B hB)
  rw [hN, hFin.encard_eq_coe_toFinset_card, hFilter]
  rfl
