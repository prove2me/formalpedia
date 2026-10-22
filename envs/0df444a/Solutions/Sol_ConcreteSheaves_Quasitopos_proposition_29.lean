-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_29
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:40:35.841637+00:00
-- url     : https://prove2.me/submissions/fa609068-6e2c-4d6d-93fb-3fbe2dec615c

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    ∀ X : D, IsDSpace K T (yoneda.obj X) := by
  intro X
  refine ⟨hK.subcanonical X, ?_⟩
  intro E φ ψ h
  apply hK.faithful
  intro x
  have := congrFun h x
  simpa using this
