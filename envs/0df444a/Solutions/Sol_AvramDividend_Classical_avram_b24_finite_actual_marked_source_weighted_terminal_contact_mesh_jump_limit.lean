-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:23:29.236135+00:00
-- url     : https://prove2.me/submissions/d8d01374-2b3f-41b2-b47e-e0d084e1e789

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
import Theorems.Thm_AvramDividend_Classical_avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (d : ℝ)
    (Jsmall : ℝ≥0 → ℝ) (T t : ℝ≥0)
    (ht0 : 0 < t) (htT : t ≤ T)
    (hPath : ∀ v : ℝ≥0, v ≤ T →
      Jsmall v =
        (∑ u ∈ S,
          if u ≤ v then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d)
    (hRight : ContinuousWithinAt Jsmall (Ici t) t)
    (a b : ℕ → ℝ≥0) (W : ℕ → ℝ) (Wleft : ℝ)
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (𝓝[Ici t] t))
    (hW : Tendsto W atTop (𝓝 Wleft)) :
    Tendsto (fun k => W k * (Jsmall (b k) - Jsmall (a k))) atTop
      (𝓝 (Wleft * (if t ∈ S then
        (if -1 < z t ∧ z t < 0 then z t else 0) else 0)))  := by
  obtain ⟨hLeft, hJump⟩ :=
    avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
      S z d Jsmall T t ht0 htT hPath
  have hLimit :=
    avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
      Jsmall t
      ((∑ u ∈ S, if u < t then
        (if -1 < z u ∧ z u < 0 then z u else 0) else 0) - (t : ℝ) * d)
      a b W Wleft hRight hLeft ha hb hW
  rw [hJump] at hLimit
  exact hLimit
