-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.marginal_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:21.793147+00:00
-- url     : https://prove2.me/submissions/5800e4d0-e172-408f-a35e-c65bc36401f6

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem solution (f : Objective n) {X Y : Finset (Fin n)} (hYX : Y ⊆ X) (e : Fin n) :
    f.value (insert e X) - f.value X ≤ f.value (insert e Y) - f.value Y := by
  by_cases heX : e ∈ X
  · rw [Finset.insert_eq_of_mem heX, sub_self]
    exact sub_nonneg.mpr (f.monotone _ _ (Finset.subset_insert e Y))
  · have hsub := f.submodular X (insert e Y)
    have hu : X ∪ insert e Y = insert e X := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (hx | rfl | hx)
        · exact Or.inr hx
        · exact Or.inl rfl
        · exact Or.inr (hYX hx)
      · rintro (rfl | hx)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hx
    have hi : X ∩ insert e Y = Y := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, rfl | hy⟩
        · exact absurd hx heX
        · exact hy
      · intro hy
        exact ⟨hYX hy, Or.inr hy⟩
    rw [hu, hi] at hsub
    linarith

end
