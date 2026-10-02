-- Prove2me | solution 1 for CirclePackingConstants.thirty_six_left_bottom_expand_to_three_sides
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:59:43.29409+00:00
-- url     : https://prove2.me/submissions/961e3941-77f2-444e-a1a8-95945a95edfb

import Mathlib
import Definitions.Def_CirclePackingConstants

set_option autoImplicit false

open CirclePackingConstants in
theorem solution :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      (∃ i, (p i).1 = 0) →
      (∃ j, (p j).2 = 0) →
      (∃ k, (p k).1 ≠ 0 ∨ (p k).2 ≠ 0) →
      ∃ q : Fin 36 → Point,
        (∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1) ∧
        (∀ i j, sqDist (p i) (p j) ≤ sqDist (q i) (q j)) ∧
        (∃ i, (q i).1 = 0) ∧
        (∃ j, (q j).2 = 0) ∧
        ((∃ i, (q i).1 = 1) ∨ (∃ j, (q j).2 = 1)) := by
  intro p hbox ⟨i1, hi1⟩ ⟨j1, hj1⟩ ⟨k, hk⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => max (p i).1 (p i).2)
  set M := max (p i0).1 (p i0).2 with hMdef
  have hMpos : 0 < M := by
    have hkpos : 0 < max (p k).1 (p k).2 := by
      obtain ⟨a0, -, b0, -⟩ := hbox k
      rcases hk with h | h
      · exact lt_of_lt_of_le (lt_of_le_of_ne a0 (Ne.symm h)) (le_max_left _ _)
      · exact lt_of_lt_of_le (lt_of_le_of_ne b0 (Ne.symm h)) (le_max_right _ _)
    exact lt_of_lt_of_le hkpos (hi0 k)
  have hM1 : M ≤ 1 := max_le (hbox i0).2.1 (hbox i0).2.2.2
  refine ⟨fun i => ((p i).1 / M, (p i).2 / M), ?_, ?_, ⟨i1, ?_⟩, ⟨j1, ?_⟩, ?_⟩
  · intro i
    obtain ⟨a0, -, b0, -⟩ := hbox i
    refine ⟨div_nonneg a0 hMpos.le, ?_, div_nonneg b0 hMpos.le, ?_⟩
    · exact (div_le_one hMpos).mpr (le_trans (le_max_left _ _) (hi0 i))
    · exact (div_le_one hMpos).mpr (le_trans (le_max_right _ _) (hi0 i))
  · intro i j
    have heq : sqDist ((p i).1 / M, (p i).2 / M) ((p j).1 / M, (p j).2 / M)
        = sqDist (p i) (p j) / M ^ 2 := by
      unfold sqDist
      field_simp
    show sqDist (p i) (p j) ≤ sqDist ((p i).1 / M, (p i).2 / M) ((p j).1 / M, (p j).2 / M)
    rw [heq]
    have hnn : 0 ≤ sqDist (p i) (p j) := by unfold sqDist; positivity
    exact le_div_self hnn (by positivity) (by nlinarith)
  · show (p i1).1 / M = 0
    rw [hi1, zero_div]
  · show (p j1).2 / M = 0
    rw [hj1, zero_div]
  · rcases le_total (p i0).2 (p i0).1 with h | h
    · left
      refine ⟨i0, ?_⟩
      show (p i0).1 / M = 1
      have : M = (p i0).1 := max_eq_left h
      rw [← this]; exact div_self hMpos.ne'
    · right
      refine ⟨i0, ?_⟩
      show (p i0).2 / M = 1
      have : M = (p i0).2 := max_eq_right h
      rw [← this]; exact div_self hMpos.ne'
