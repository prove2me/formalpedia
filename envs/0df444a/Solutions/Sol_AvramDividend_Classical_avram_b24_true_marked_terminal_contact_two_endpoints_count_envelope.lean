-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:28:06.312199+00:00
-- url     : https://prove2.me/submissions/27ecd258-11c1-4c3d-abc4-98710177cdd7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (B L Ja Jb W Wleft z : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hJa : ‖Ja‖ ≤ B) (hJb : ‖Jb‖ ≤ B)
    (hW : ‖W‖ ≤ L) (hWleft : ‖Wleft‖ ≤ L) :
    ‖W * (Jb - Ja) -
      Wleft * (if -1 < z ∧ z < 0 then z else 0)‖ ≤
      2 * L * B + L := by
  have hJ : ‖Jb - Ja‖ ≤ 2 * B := by
    calc
      ‖Jb - Ja‖ ≤ ‖Jb‖ + ‖Ja‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add hJb hJa
      _ = 2 * B := by ring
  have hMark :
      ‖if -1 < z ∧ z < 0 then z else 0‖ ≤ (1 : ℝ) := by
    by_cases hsm : -1 < z ∧ z < 0
    · simp only [if_pos hsm, Real.norm_eq_abs]
      rw [abs_of_nonpos (le_of_lt hsm.2)]
      linarith [hsm.1]
    · simp [hsm]
  have hFirst : ‖W * (Jb - Ja)‖ ≤ L * (2 * B) := by
    rw [norm_mul]
    exact mul_le_mul hW hJ (norm_nonneg _) hL
  have hSecond :
      ‖Wleft * (if -1 < z ∧ z < 0 then z else 0)‖ ≤ L := by
    rw [norm_mul]
    calc
      ‖Wleft‖ * ‖if -1 < z ∧ z < 0 then z else 0‖ ≤
        L * (1 : ℝ) :=
        mul_le_mul hWleft hMark (norm_nonneg _) hL
      _ = L := by ring
  calc
    ‖W * (Jb - Ja) -
      Wleft * (if -1 < z ∧ z < 0 then z else 0)‖ ≤
        ‖W * (Jb - Ja)‖ +
          ‖Wleft * (if -1 < z ∧ z < 0 then z else 0)‖ :=
      norm_sub_le _ _
    _ ≤ L * (2 * B) + L := add_le_add hFirst hSecond
    _ = 2 * L * B + L := by ring
