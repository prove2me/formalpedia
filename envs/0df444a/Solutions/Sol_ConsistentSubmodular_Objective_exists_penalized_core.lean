-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_penalized_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:56.484285+00:00
-- url     : https://prove2.me/submissions/5fc1abd0-028d-4c9b-aac1-72a4543a1fc9

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (U : Finset (Fin n)) (c : ℝ) :
    ∃ D ⊆ U,
      (∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) ∧
      (∀ e ∈ D, c < f.value D - f.value (D.erase e)) := by
  classical
  let score := fun D : Finset (Fin n) => f.value D - c * D.card
  obtain ⟨D₀, hD₀, hmax₀⟩ := U.powerset.exists_max_image score ⟨∅, by simp⟩
  let maximizers := U.powerset.filter (fun D => score D = score D₀)
  have hnonempty : maximizers.Nonempty := ⟨D₀, by simp [maximizers, hD₀]⟩
  obtain ⟨D, hD, hmin⟩ := maximizers.exists_min_image Finset.card hnonempty
  have hDU : D ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
  have hDscore : score D = score D₀ := (Finset.mem_filter.mp hD).2
  have hmax : ∀ A ⊆ U, score A ≤ score D := by
    intro A hAU
    rw [hDscore]
    exact hmax₀ A (Finset.mem_powerset.mpr hAU)
  refine ⟨D, hDU, ?_, ?_⟩
  · intro e heU heD
    have h := hmax (insert e D) (Finset.insert_subset heU hDU)
    have hc : ((insert e D).card : ℝ) = (D.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem heD]
      push_cast
      rfl
    dsimp [score] at h
    rw [hc] at h
    linarith
  · intro e heD
    have hsub : D.erase e ⊆ U := (Finset.erase_subset e D).trans hDU
    have hweak := hmax (D.erase e) hsub
    have hstrict : score (D.erase e) < score D := by
      apply lt_of_le_of_ne hweak
      intro heq
      have hmem : D.erase e ∈ maximizers := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, heq.trans hDscore⟩
      have hcard := hmin (D.erase e) hmem
      have hlt := Finset.card_erase_lt_of_mem heD
      omega
    have hc : ((D.erase e).card : ℝ) + 1 = (D.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one heD
    dsimp [score] at hstrict
    rw [← hc] at hstrict
    nlinarith only [hstrict]

end
