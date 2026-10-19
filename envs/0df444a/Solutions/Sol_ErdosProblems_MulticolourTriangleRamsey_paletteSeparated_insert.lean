-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteSeparated_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/e8987147-f284-4082-b8ea-61f893690f09

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {α : Type*} [DecidableEq α]
    {s : ℕ} {family : Finset (Finset α)} {P : Finset α}
    (hseparated : IsPaletteSeparated s family)
    (hequal : ∀ Q ∈ family, Q.card = P.card)
    (hfar : ∀ Q ∈ family, s ≤ (P \ Q).card) :
    IsPaletteSeparated s (insert P family) := by
  classical
  intro X hX Y hY hXY
  by_cases hXP : X = P
  · subst X
    by_cases hYP : Y = P
    · exact (hXY hYP.symm).elim
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hfar Y hYfamily
  · have hXfamily : X ∈ family :=
      (Finset.mem_insert.mp hX).resolve_left hXP
    by_cases hYP : Y = P
    · subst Y
      rw [Finset.card_sdiff_comm (hequal X hXfamily)]
      exact hfar X hXfamily
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hseparated X hXfamily Y hYfamily hXY
end ErdosProblems.MulticolourTriangleRamsey
