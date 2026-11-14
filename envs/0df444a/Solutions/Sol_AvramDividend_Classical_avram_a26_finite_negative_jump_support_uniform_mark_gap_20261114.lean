-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:36:26.729265+00:00
-- url     : https://prove2.me/submissions/edf2a0e8-9a2c-48ad-aca7-ac05bab1add2

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal
noncomputable section

/-- Finite strictly negative jump support is uniformly separated from zero on every finite horizon. -/
theorem solution
    (F : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hFinite : {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ F u ≠ 0}.Finite)
    (hNegative : ∀ u : ℝ≥0, 0 < u → u ≤ T → F u ≠ 0 → F u < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T → F u ≠ 0 → F u ≤ -ε := by
  have hMargin (S : Finset ℝ≥0) (hS : ∀ u ∈ S, F u < 0) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ S, F u ≤ -ε := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp
    | @insert a S ha ih =>
      have hSa : F a < 0 := hS a (Finset.mem_insert_self a S)
      have hSS : ∀ u ∈ S, F u < 0 := by
        intro u hu
        exact hS u (Finset.mem_insert_of_mem hu)
      obtain ⟨ε, hε, hBound⟩ := ih hSS
      refine ⟨min ε (-F a), lt_min hε (neg_pos.mpr hSa), ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · have hm := min_le_right ε (-F u)
        nlinarith
      · have hm := min_le_left ε (-F a)
        have hb := hBound u hu
        nlinarith
  have hS : ∀ u ∈ hFinite.toFinset, F u < 0 := by
    intro u hu
    obtain ⟨hu0, huT, huF⟩ := hFinite.mem_toFinset.mp hu
    exact hNegative u hu0 huT huF
  obtain ⟨ε, hε, hBound⟩ := hMargin hFinite.toFinset hS
  refine ⟨ε, hε, ?_⟩
  intro u hu0 huT huF
  exact hBound u (hFinite.mem_toFinset.mpr ⟨hu0, huT, huF⟩)
