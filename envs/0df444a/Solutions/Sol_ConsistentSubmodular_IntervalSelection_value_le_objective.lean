-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.value_le_objective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:26.580946+00:00
-- url     : https://prove2.me/submissions/27284831-8ee4-449a-8266-1431a192414c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_IntervalSelection

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.IntervalSelection

section Objective

variable {n : ℕ} (f : Objective n)

/-- Diminishing returns for nested sets `A ⊆ B`:
`f(X ∪ B) - f(B) ≤ f(X ∪ A) - f(A)`. -/
theorem diminishing {A B : Finset (Fin n)} (hAB : A ⊆ B) (X : Finset (Fin n)) :
    f.value (X ∪ B) + f.value A ≤ f.value (X ∪ A) + f.value B := by
  have h := f.submodular (X ∪ A) B
  have hunion : X ∪ A ∪ B = X ∪ B := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr hAB]
  have hinter : A ⊆ (X ∪ A) ∩ B := fun e he =>
    Finset.mem_inter.mpr ⟨Finset.mem_union_right X he, hAB he⟩
  have hmono := f.monotone A ((X ∪ A) ∩ B) hinter
  rw [hunion] at h
  linarith

end Objective

end ConsistentSubmodular.IntervalSelection

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem solution (p : Point W.lastStage) (hp : IsSimplex p)
    (i j : Fin (W.lastStage + 1)) :
    (windowIntervals W p hp).value i j ≤ W.objective.value (W.candidate i ∪ W.arrivals j) := by
  simp only [IntervalInstance.value, windowIntervals, WindowInstance.benchmark]
  rcases le_total j i with hji | hij
  · have hR := W.arrivals_mono hji
    have hl := W.objective.monotone _ _ hR
    have hd := diminishing W.objective hR (W.candidate i)
    have hr := W.objective.monotone (W.arrivals i) (W.candidate i ∪ W.arrivals i)
      Finset.subset_union_right
    rw [max_eq_left hl, max_eq_right (sub_nonneg.mpr hr)]
    linarith
  · have hR := W.arrivals_mono hij
    have hl := W.objective.monotone _ _ hR
    have h1 := W.objective.monotone (W.arrivals j) (W.candidate i ∪ W.arrivals j)
      Finset.subset_union_right
    have h2 := W.objective.monotone (W.candidate i ∪ W.arrivals i)
      (W.candidate i ∪ W.arrivals j) (Finset.union_subset_union_right hR)
    rw [max_eq_right hl]
    rcases le_total 0 (W.objective.value (W.candidate i ∪ W.arrivals i) -
        W.objective.value (W.arrivals j)) with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith

end
