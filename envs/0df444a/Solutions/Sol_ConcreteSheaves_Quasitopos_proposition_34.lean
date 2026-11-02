-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_34
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:01:33.399709+00:00
-- url     : https://prove2.me/submissions/b41a293f-8394-4fe6-88a9-0ada6cb21eec

import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_29
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_31
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_39
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.Choose

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

private theorem component_injective (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {A X : DSpace K T} (i : A ⟶ X)
    [Mono i] (E : Dᵒᵖ) : Function.Injective (i.hom.app E) := by
  intro a b hab
  apply A.property.2 E.unop
  funext d
  apply ((proposition_31 K T hT hK i).1.mp inferInstance)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hab]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {A X : DSpace K T} (i : A ⟶ X) :
    StrongMono i ↔ IsSubspace i := by
  classical
  constructor
  · intro hi
    have : StrongMono i := hi
    have hlim := proposition_39 K T hT hK
    have : HasLimits (DSpace K T) := hlim.1
    have : PreservesLimits (IsDSpace K T).ι := hlim.2
    have : PreservesLimits (underlying K T) := by
      unfold underlying
      infer_instance
    intro E φ hφ
    let yE : DSpace K T := ⟨yoneda.obj E, proposition_29 K T hT hK E⟩
    let g : yE ⟶ X := ObjectProperty.homMk (yonedaEquiv.symm φ)
    let p : pullback i g ⟶ yE := pullback.snd i g
    have hp : Epi p := (proposition_31 K T hT hK p).2.mpr (by
      intro d
      obtain ⟨a, ha⟩ := hφ d
      have hpb := (underlying K T).map_isPullback (IsPullback.of_hasPullback i g)
      obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback hpb a d ha
      exact ⟨z, hz⟩)
    let sq : CommSq (pullback.fst i g) p i g := ⟨pullback.condition⟩
    have hplot : i.hom.app (op E) (sq.lift.hom.app (op E) (𝟙 E)) = φ := by
      have h := congrArg (fun f : yE ⟶ X => f.hom.app (op E) (𝟙 E)) sq.fac_right
      change i.hom.app (op E) (sq.lift.hom.app (op E) (𝟙 E)) =
        X.obj.map (𝟙 (op E)) φ at h
      exact h.trans (X.obj.map_id_apply (op E) φ)
    refine ⟨sq.lift.hom.app (op E) (𝟙 E), hplot, ?_⟩
    intro ψ hψ
    exact component_injective K T hT hK i (op E) (hψ.trans hplot.symm)
  · intro hi
    have hinj (E : Dᵒᵖ) : Function.Injective (i.hom.app E) := by
      intro a b hab
      have hr : ∀ d : T ⟶ E.unop,
          X.obj.map d.op (i.hom.app E a) ∈ Set.range (i.hom.app (op T)) := by
        intro d
        exact ⟨A.obj.map d.op a, NatTrans.naturality_apply i.hom d.op a⟩
      obtain ⟨ψ, hψ, huniq⟩ := hi (i.hom.app E a) hr
      exact (huniq a rfl).trans (huniq b hab.symm).symm
    have hm : Mono i := (proposition_31 K T hT hK i).1.mpr (hinj (op T))
    refine { mono := hm, rlp := ?_ }
    intro B C p hp
    refine ⟨?_⟩
    intro f g sq
    have hs := (proposition_31 K T hT hK p).2.mp hp
    have lifts (E : Dᵒᵖ) (φ : C.obj.obj E) :
        ∃! ψ : A.obj.obj E, i.hom.app E ψ = g.hom.app E φ := by
      apply hi
      intro d
      obtain ⟨b, hb⟩ := hs (C.obj.map d.op φ)
      refine ⟨f.hom.app (op T) b, ?_⟩
      calc
        i.hom.app (op T) (f.hom.app (op T) b) =
            g.hom.app (op T) (p.hom.app (op T) b) := by
          exact congrArg (fun q : B ⟶ X => q.hom.app (op T) b) sq.w
        _ = g.hom.app (op T) (C.obj.map d.op φ) := by rw [hb]
        _ = X.obj.map d.op (g.hom.app E φ) := NatTrans.naturality_apply g.hom d.op φ
    choose l hl huniq using lifts
    let t : C ⟶ A := ObjectProperty.homMk {
      app := fun E => ↾(l E)
      naturality := by
        intro E F a
        ext φ
        apply hinj F
        change i.hom.app F (l F (C.obj.map a φ)) =
          i.hom.app F (A.obj.map a (l E φ))
        rw [hl, NatTrans.naturality_apply i.hom a (l E φ), hl]
        exact NatTrans.naturality_apply g.hom a φ }
    have ht : t ≫ i = g := by
      apply InducedCategory.hom_ext
      ext E φ
      exact hl E φ
    exact CommSq.HasLift.mk' {
      l := t
      fac_left := by
        apply (cancel_mono i).mp
        rw [Category.assoc, ht]
        exact sq.w.symm
      fac_right := ht }
