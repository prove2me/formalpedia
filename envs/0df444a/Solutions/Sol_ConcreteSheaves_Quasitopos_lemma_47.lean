-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.lemma_47
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:49:45.39399+00:00
-- url     : https://prove2.me/submissions/0064ec90-1386-4640-b78f-3ecce6316de7

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

lemma conc_map {T : D} {P : Dᵒᵖ ⥤ Type u} {X Y : D} (g : Y ⟶ X)
    (h : (concretization T P).obj (op X)) :
    ((concretization T P).map g.op h).1 = fun d => h.1 (d ≫ g) := rfl

lemma conc_pi {T : D} {P : Dᵒᵖ ⥤ Type u} {X : D} (φ : P.obj (op X)) :
    ((concretizationπ T P).app (op X) φ).1 = fun d : T ⟶ X => P.map d.op φ := rfl

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) :
    IsConcrete T (concretization T P) ∧
      ∀ (Q : Dᵒᵖ ⥤ Type u), IsConcrete T Q → ∀ f : P ⟶ Q,
        ∃! g : concretization T P ⟶ Q, concretizationπ T P ≫ g = f := by
  refine ⟨?_, ?_⟩
  · intro X h h' e
    apply Subtype.ext
    funext d
    have := congrArg (fun k => (k : (concretization T P).obj (op T)).1 (𝟙 T)) (congrFun e d)
    simp only [conc_map, Category.id_comp] at this
    exact this
  · intro Q hQ f
    -- well-definedness
    have wd : ∀ (X : D) (φ φ' : P.obj (op X)),
        (fun d : T ⟶ X => P.map d.op φ) = (fun d : T ⟶ X => P.map d.op φ') →
          f.app (op X) φ = f.app (op X) φ' := by
      intro X φ φ' e
      apply hQ X
      funext d
      show Q.map d.op (f.app (op X) φ) = Q.map d.op (f.app (op X) φ')
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      exact congrArg (f.app (op T)) (congrFun e d)
    let gfun : ∀ X : Dᵒᵖ, (concretization T P).obj X → Q.obj X := fun X h =>
      f.app X h.2.choose
    have gspec : ∀ (X : D) (φ : P.obj (op X)),
        gfun (op X) ((concretizationπ T P).app (op X) φ) = f.app (op X) φ := by
      intro X φ
      apply wd X
      have := ((concretizationπ T P).app (op X) φ).2.choose_spec
      exact this
    let g : concretization T P ⟶ Q :=
      { app := fun X => ↾(gfun X)
        naturality := by
          intro X Y k
          ext h
          obtain ⟨φ, hφ⟩ := h.2
          have hh : h = (concretizationπ T P).app X φ := Subtype.ext hφ.symm
          subst hh
          show gfun Y ((concretization T P).map k ((concretizationπ T P).app X φ)) =
            Q.map k (gfun X ((concretizationπ T P).app X φ))
          have := NatTrans.naturality_apply (concretizationπ T P) k φ
          rw [← this]
          rw [gspec Y.unop, gspec X.unop, NatTrans.naturality_apply] }
    refine ⟨g, ?_, ?_⟩
    · ext X φ
      exact gspec X.unop φ
    · intro g' hg'
      ext X h
      obtain ⟨φ, hφ⟩ := h.2
      have hh : h = (concretizationπ T P).app X φ := Subtype.ext hφ.symm
      subst hh
      show g'.app X ((concretizationπ T P).app X φ) = gfun X ((concretizationπ T P).app X φ)
      rw [gspec X.unop]
      have := congrArg (fun k => k.app X φ) hg'
      simpa using this
