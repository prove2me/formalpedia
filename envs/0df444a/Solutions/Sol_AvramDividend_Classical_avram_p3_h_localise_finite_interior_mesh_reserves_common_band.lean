-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_localise_finite_interior_mesh_reserves_common_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:13:28.898462+00:00
-- url     : https://prove2.me/submissions/a09e7d26-48a6-4269-8680-fdc56b2df5bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite nonempty original BV mesh of strict interior reserve states
shares one compact positive-cap strip. The same a ≤ 2 cutoff bounds apply
to all mesh cells, even for an infinite reserve cap. -/
theorem solution
    (C : ℝ≥0∞) (S : Finset ℝ) (hS : S.Nonempty)
    (hInside : ∀ z ∈ S, 0 < z ∧ ENNReal.ofReal z < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      (∀ z ∈ S, z ∈ Icc a b) ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  classical
  let m : ℝ := S.min' hS
  let b : ℝ := S.max' hS
  have hmS : m ∈ S := Finset.min'_mem S hS
  have hbS : b ∈ S := Finset.max'_mem S hS
  have hm : 0 < m := (hInside m hmS).1
  have hbC : ENNReal.ofReal b < C := (hInside b hbS).2
  let a : ℝ := min (m / 2) 1
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have ha2 : a ≤ 2 := by
    have h := min_le_right (m / 2) (1 : ℝ)
    dsimp [a]
    linarith
  have ham : a ≤ m := by
    have h := min_le_left (m / 2) (1 : ℝ)
    dsimp [a]
    linarith
  have hab : a ≤ b :=
    le_trans ham (Finset.le_max' S m hmS)
  refine ⟨a, b, ha, ha2, hab, ?_, ?_⟩
  · intro z hz
    exact ⟨le_trans ham (Finset.min'_le S z hz),
      Finset.le_max' S z hz⟩
  · intro y hy
    change 0 < y ∧ ENNReal.ofReal y < C
    constructor
    · exact lt_of_lt_of_le (half_pos ha) hy.1
    · exact lt_of_le_of_lt (ENNReal.ofReal_mono hy.2) hbC
