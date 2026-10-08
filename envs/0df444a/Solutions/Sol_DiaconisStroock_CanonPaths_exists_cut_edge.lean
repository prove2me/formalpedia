-- Prove2me | solution 1 for DiaconisStroock.CanonPaths.exists_cut_edge
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:40:00.177777+00:00
-- url     : https://prove2.me/submissions/206e8095-ecda-4e09-ab8a-04cde09f11bb

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

open DiaconisStroock.Poincare

theorem solution {V : Type*} [DecidableEq V] (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∉ S) (p : List V)
    (hp : p.head? = some x) (hp' : p.getLast? = some y) :
    ∃ e ∈ DiaconisStroock.Poincare.pathEdges p, e.1 ∈ S ∧ e.2 ∉ S := by
  induction p generalizing x with
  | nil => simp at hp
  | cons a p ih =>
    simp only [List.head?_cons, Option.some.injEq] at hp
    subst x
    cases p with
    | nil =>
      simp at hp'
      subst y
      exact (hy hx).elim
    | cons b p =>
      by_cases hb : b ∈ S
      · obtain ⟨e, he, h1, h2⟩ := ih b hb rfl (by simpa using hp')
        exact ⟨e, by simpa [pathEdges] using Or.inr he, h1, h2⟩
      · exact ⟨(a,b), by simp [pathEdges], hx, hb⟩

#print axioms solution
