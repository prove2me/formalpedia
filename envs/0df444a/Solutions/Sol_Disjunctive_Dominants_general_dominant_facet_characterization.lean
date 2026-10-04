-- Prove2me | solution 1 for Disjunctive.Dominants.general_dominant_facet_characterization
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:30:02.234079+00:00
-- url     : https://prove2.me/submissions/73436637-c8de-4fe7-aeec-6d1720b183ef

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

open Disjunctive.Dominants

theorem solution : ¬ (∀ {n : ℕ} (P : Set (Fin n → ℝ)) (hP : P.Nonempty),
    Dominant P = {x | 0 ≤ x ∧ ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        1 ≤ dotProduct pi x} ∧
      ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1})) := by
  intro h
  set e1 : Fin 2 → ℝ := ![1, 0] with he1
  set e2 : Fin 2 → ℝ := ![0, 1] with he2
  set P : Set (Fin 2 → ℝ) := {e1, e2} with hP
  set z : Fin 2 → ℝ := ![1 / 2, 1 / 2] with hz
  have heq := (h P ⟨e1, by simp [hP]⟩).1
  have hzR : z ∈ {x : Fin 2 → ℝ | 0 ≤ x ∧ ∀ (S : Finset (Fin 2)) (pi : Fin 2 → ℝ),
      IsInIS S P pi → 1 ≤ dotProduct pi x} := by
    refine ⟨fun i => by fin_cases i <;> simp [hz] <;> norm_num, fun S pi hpi => ?_⟩
    obtain ⟨-, -, hval, -⟩ := hpi
    have h1 := hval e1 ⟨e1, by simp [hP], fun _ _ => rfl⟩
    have h2 := hval e2 ⟨e2, by simp [hP], fun _ _ => rfl⟩
    simp [dotProduct, Fin.sum_univ_two, he1, he2] at h1 h2
    simp [dotProduct, Fin.sum_univ_two, hz]
    linarith
  rw [← heq] at hzR
  obtain ⟨-, x, hx, hxz⟩ := hzR
  rcases hx with rfl | rfl
  · have := hxz 0; simp [he1, hz] at this; norm_num at this
  · have := hxz 1; simp [he2, hz] at this; norm_num at this

#print axioms solution
