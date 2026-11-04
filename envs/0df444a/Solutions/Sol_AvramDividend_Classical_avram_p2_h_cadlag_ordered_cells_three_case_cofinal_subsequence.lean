-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_cofinal_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:27:56.773259+00:00
-- url     : https://prove2.me/submissions/5ec7d5ff-f7ed-45eb-b67d-2abe15b64d18

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_ordered_cells_three_case_frequently

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Extract a cofinal subsequence on which exactly one sided positional
case holds at every index, retaining both endpoint limits. -/
theorem solution
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hab : ∀ n, a n ≤ b n)
    (ha : Tendsto a atTop (𝓝 t))
    (hb : Tendsto b atTop (𝓝 t)) :
    ∃ φ : ℕ → ℕ,
      Tendsto φ atTop (atTop : Filter ℕ) ∧
      Tendsto (a ∘ φ) atTop (𝓝 t) ∧
      Tendsto (b ∘ φ) atTop (𝓝 t) ∧
      ((∀ n, b (φ n) < t) ∨
       (∀ n, t ≤ a (φ n)) ∨
       (∀ n, a (φ n) < t ∧ t ≤ b (φ n))) := by
  rcases avram_p2_h_cadlag_ordered_cells_three_case_frequently
      a b t hab with hleft | hright | hcross
  · obtain ⟨φ, hφ, hc⟩ :=
      Filter.exists_seq_forall_of_frequently hleft
    exact ⟨φ, hφ, ha.comp hφ, hb.comp hφ, Or.inl hc⟩
  · obtain ⟨φ, hφ, hc⟩ :=
      Filter.exists_seq_forall_of_frequently hright
    exact ⟨φ, hφ, ha.comp hφ, hb.comp hφ, Or.inr (Or.inl hc)⟩
  · obtain ⟨φ, hφ, hc⟩ :=
      Filter.exists_seq_forall_of_frequently hcross
    exact ⟨φ, hφ, ha.comp hφ, hb.comp hφ, Or.inr (Or.inr hc)⟩
