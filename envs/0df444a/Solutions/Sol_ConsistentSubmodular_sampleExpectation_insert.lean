-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:18.067194+00:00
-- url     : https://prove2.me/submissions/d9c1f507-8d26-46e0-9a38-12df370a37e4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation (insert e U) p v =
      (1 - p e) * sampleExpectation U p v + p e * sampleExpectation U p (fun S => v (insert e S)) := by
  unfold sampleExpectation
  rw [Finset.sum_powerset_insert he]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    have hSU := Finset.mem_powerset.mp hS
    have heS : e ∉ S := fun h => he (hSU h)
    have hd : (insert e U) \ S = insert e (U \ S) := by
      ext i
      by_cases hie : i = e <;> simp [hie, heS]
    unfold subsetWeight
    rw [hd, Finset.prod_insert (by simp [he])]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    have hSU := Finset.mem_powerset.mp hS
    have heS : e ∉ S := fun h => he (hSU h)
    have hd : (insert e U) \ insert e S = U \ S := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, hn⟩
        · exact (hn (Or.inl hi)).elim
        · exact ⟨hi, fun h => hn (Or.inr h)⟩
      · rintro ⟨hi, hn⟩
        exact ⟨Or.inr hi, by rintro (rfl | h); exact he hi; exact hn h⟩
    unfold subsetWeight
    rw [hd, Finset.prod_insert heS]
    ring

end
