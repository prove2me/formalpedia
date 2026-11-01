-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_pi_system_boolean_indicator_span
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:24:36.233579+00:00
-- url     : https://prove2.me/submissions/e0f55162-b776-4a24-a599-2a2ae10b895f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_boolean_indicator_span_of_inter_closed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- For an arbitrary Pi-system, every indicator of its finite Boolean algebra
has a finite real linear representation by Pi-system generators, plus the
constant indicator of the full space. Empty sets may be adjoined freely. -/
theorem solution
    {α : Type*} (G : Set (Set α))
    (hPi : IsPiSystem G)
    (s : Set α) (hs : s ∈ generateSetAlgebra G) :
    let GP : Set (Set α) :=
      insert Set.univ (insert (∅ : Set α) G)
    let χ : Set α → (α → ℝ) :=
      fun t => Set.indicator t (fun _ => (1 : ℝ))
    χ s ∈ Submodule.span ℝ
      {v : α → ℝ | ∃ (t : Set α), t ∈ GP ∧ χ t = v} := by
  classical
  let GP : Set (Set α) :=
    insert Set.univ (insert (∅ : Set α) G)
  let χ : Set α → (α → ℝ) :=
    fun t => Set.indicator t (fun _ => (1 : ℝ))
  change χ s ∈ Submodule.span ℝ
    {v : α → ℝ | ∃ (t : Set α), t ∈ GP ∧ χ t = v}
  have hPiGP : IsPiSystem GP := (hPi.insert_empty).insert_univ
  have hClosed : ∀ (u : Set α), u ∈ GP →
      ∀ (v : Set α), v ∈ GP → u ∩ v ∈ GP := by
    intro u hu v hv
    by_cases hne : (u ∩ v).Nonempty
    · exact hPiGP u hu v hv hne
    · have he : u ∩ v = (∅ : Set α) :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp [GP]
  have hSub : G ⊆ GP := by
    intro t ht
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ht)
  have hsGP : s ∈ generateSetAlgebra GP :=
    generateSetAlgebra_mono hSub hs
  exact avram_wave4_p1_boolean_indicator_span_of_inter_closed
    GP hClosed (by simp [GP]) s hsGP
