-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.lemma_48
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:41:56.576356+00:00
-- url     : https://prove2.me/submissions/3463d5a2-25a0-4fcb-9f60-952f629aa939

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) (hP : IsConcrete T P) :
    ∀ ⦃X : D⦄ (R : Presieve X), R ∈ K X → Presieve.IsSeparatedFor P R := by
  intro X R hR x t1 t2 h1 h2
  apply hP X
  funext d
  obtain ⟨Y, f, hf, y, rfl⟩ := hK.jointlySurj R hR d
  show P.map (y ≫ f).op t1 = P.map (y ≫ f).op t2
  rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h1 f hf, h2 f hf]
