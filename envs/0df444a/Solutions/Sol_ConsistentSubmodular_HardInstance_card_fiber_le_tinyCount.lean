-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.card_fiber_le_tinyCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:51.011651+00:00
-- url     : https://prove2.me/submissions/a3a33831-a323-4e59-bd63-a97177b5bbe2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem solution {k : ℕ} (S : Finset (Fin (3 * k + 2))) (g : Fin 3)
    (hfull : ∀ e ∈ S, e.val ≠ 3 * k + g.val) :
    (fiber (S.biUnion (elementCells k)) g).card ≤ tinyCount k g S := by
  refine card_le_card_of_injOn tinyAt ?_ ?_
  · intro c hc
    obtain ⟨hcS, hcg⟩ := mem_filter.mp (mem_coe.mp hc)
    obtain ⟨e, he, hce⟩ := mem_biUnion.mp hcS
    have hce' := (mem_filter.mp hce).2
    refine mem_coe.mpr (mem_filter.mpr ?_)
    by_cases hlt : e.val < 3 * k
    · rw [if_pos hlt] at hce'
      obtain ⟨h1, h2⟩ := hce'
      have hdiv := Nat.div_add_mod e.val k
      have heq : tinyAt c = e := by
        apply Fin.ext
        simp only [tinyAt]
        rw [h1, h2]
        linarith [Nat.mul_comm k (e.val / k)]
      rw [heq]
      exact ⟨he, hlt, by rw [← h1, hcg]⟩
    · rw [if_neg hlt] at hce'
      exfalso
      by_cases h3k : e.val = 3 * k
      · rw [if_pos h3k] at hce'
        exact hfull e he (by rw [h3k, ← hcg, hce']; rfl)
      · rw [if_neg h3k] at hce'
        have he2 := e.isLt
        exact hfull e he (by rw [← hcg, hce']; omega)
  · intro c hc c' hc' h
    have h1 := (mem_filter.mp (mem_coe.mp hc)).2
    have h2 := (mem_filter.mp (mem_coe.mp hc')).2
    have hv := congrArg Fin.val h
    simp only [tinyAt] at hv
    rw [h1, ← h2] at hv
    exact Prod.ext (h1.trans h2.symm) (Fin.ext (by omega))

end
