-- Prove2me | solution 1 for DynTypeMatching.Priority.respects_of_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:36:42.372123+00:00
-- url     : https://prove2.me/submissions/2bfdf111-33b8-4fd1-9e58-3ea852af29c9

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

open DynTypeMatching.Priority in
theorem solution {m n : ℕ} (M : Model m n) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Q : Fin m → Fin n → ℝ)
    (h1 : ∀ (i i' : Fin m) (j : Fin n), DomCol M i i' j → Q i' j = 0 ∨ postD x Q i = 0)
    (h2 : ∀ (i : Fin m) (j j' : Fin n), DomRow M i j j' → Q i j' = 0 ∨ postS y Q j = 0)
    (h3 : ∀ (i i' : Fin m) (j j' : Fin n), DomCol M i i' j → DomRow M i j j' →
      Q i' j = 0 ∨ Q i j' = 0) :
    Respects M x y Q := by
  classical
  constructor
  · intro i i' j hd
    by_cases hq : Q i' j = 0
    · exact Or.inl hq
    · right
      have hp := (h1 i i' j hd).resolve_left hq
      unfold postD at hp
      unfold resD
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j'' => DomRow M i j j'') (fun j'' => Q i j'')
      have hzero : ∑ j'' ∈ Finset.univ.filter (fun j'' => DomRow M i j j''), Q i j'' = 0 := by
        apply Finset.sum_eq_zero
        intro j'' hj''
        exact (h3 i i' j j'' hd (Finset.mem_filter.mp hj'').2).resolve_left hq
      linarith
  · intro i j j' hd
    by_cases hq : Q i j' = 0
    · exact Or.inl hq
    · right
      have hp := (h2 i j j' hd).resolve_left hq
      unfold postS at hp
      unfold resS
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i'' => DomCol M i i'' j) (fun i'' => Q i'' j)
      have hzero : ∑ i'' ∈ Finset.univ.filter (fun i'' => DomCol M i i'' j), Q i'' j = 0 := by
        apply Finset.sum_eq_zero
        intro i'' hi''
        exact (h3 i i'' j j' (Finset.mem_filter.mp hi'').2 hd).resolve_right hq
      linarith
