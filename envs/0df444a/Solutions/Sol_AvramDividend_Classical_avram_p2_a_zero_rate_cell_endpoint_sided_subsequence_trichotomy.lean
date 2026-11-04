-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_cell_endpoint_sided_subsequence_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:20:16.395179+00:00
-- url     : https://prove2.me/submissions/951f6646-7533-454a-919c-f51774bca63a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

theorem solution
    (a b : ℕ → ℝ≥0) (t : ℝ≥0) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n, b (g n) < t) ∨
      (∀ n, t ≤ a (g n)) ∨
      (∀ n, a (g n) < t ∧ t ≤ b (g n)) := by
  let e : ℕ → ℝ≥0 × ℝ≥0 := fun n => (a n, b n)
  let U : Set (ℝ≥0 × ℝ≥0) := {p | p.2 < t}
  let V : Set (ℝ≥0 × ℝ≥0) := {p | t ≤ p.1}
  let W : Set (ℝ≥0 × ℝ≥0) := {p | p.1 < t ∧ t ≤ p.2}
  have hcover : ∀ n, e n ∈ U ∪ (V ∪ W) := by
    intro n
    change b n < t ∨ (t ≤ a n ∨ (a n < t ∧ t ≤ b n))
    by_cases hb : b n < t
    · exact Or.inl hb
    · by_cases ha : t ≤ a n
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨lt_of_not_ge ha, le_of_not_gt hb⟩)
  obtain ⟨g, hg | hg⟩ := Nat.exists_subseq_of_forall_mem_union e hcover
  · refine ⟨g, Or.inl ?_⟩
    intro n
    simpa [e, U] using hg n
  · obtain ⟨k, hk | hk⟩ :=
      Nat.exists_subseq_of_forall_mem_union (fun n => e (g n)) hg
    · refine ⟨k.comp g, Or.inr (Or.inl ?_)⟩
      intro n
      simpa [e, V] using hk n
    · refine ⟨k.comp g, Or.inr (Or.inr ?_)⟩
      intro n
      simpa [e, W] using hk n
