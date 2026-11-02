-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_40
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:08:07.611197+00:00
-- url     : https://prove2.me/submissions/4a510e06-6b6e-4ab0-b91b-2d5061eeb69f

import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_29
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_30
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_34
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_39
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits ConcreteSheaves.Quasitopos Opposite

universe u
variable {D : Type u} [SmallCategory D]

private theorem subspace_component_injective {K : Coverage D} {T : D}
    {A X : DSpace K T} (i : A ⟶ X) (hi : IsSubspace i) (E : Dᵒᵖ) :
    Function.Injective (i.hom.app E) := by
  intro a b hab
  have hr : ∀ d : T ⟶ E.unop,
      X.obj.map d.op (i.hom.app E a) ∈ Set.range (i.hom.app (op T)) := by
    intro d
    exact ⟨A.obj.map d.op a, NatTrans.naturality_apply i.hom d.op a⟩
  obtain ⟨ψ, hψ, hu⟩ := hi (i.hom.app E a) hr
  exact (hu a rfl).trans (hu b hab.symm).symm

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    HasWeakSubobjectClassifier (DSpace K T) := by
  classical
  have : PreservesLimits (IsDSpace K T).ι := (proposition_39 K T hT hK).2
  let one : DSpace K T := ⟨yoneda.obj T, proposition_29 K T hT hK T⟩
  let Ω : DSpace K T := ⟨omegaPresheaf T, proposition_30 K T hT hK⟩
  let toOne (X : DSpace K T) : X ⟶ one := ObjectProperty.homMk {
    app := fun E => ↾(fun _ => hT.from E.unop)
    naturality := by
      intro E F f
      ext φ
      exact hT.hom_ext _ _ }
  have hone : IsTerminal one := IsTerminal.ofUniqueHom toOne (by
    intro X f
    apply ObjectProperty.hom_ext
    ext E φ
    exact hT.hom_ext _ _)
  let truth : one ⟶ Ω := ObjectProperty.homMk {
    app := fun _ => ↾(fun _ _ => true)
    naturality := by intros; rfl }
  refine ⟨one, Ω, hone, truth, ?_⟩
  intro A X i hi
  have hsub := (proposition_34 K T hT hK i).1 hi
  let χ : X ⟶ Ω := ObjectProperty.homMk {
    app := fun E => ↾(fun φ d => decide (X.obj.map d.op φ ∈ Set.range (i.hom.app (op T))))
    naturality := by
      intro E F f
      ext φ
      funext d
      change decide (X.obj.map d.op (X.obj.map f φ) ∈ _) =
        decide (X.obj.map (d ≫ f.unop).op φ ∈ _)
      simp }
  have w : i ≫ χ = hone.from A ≫ truth := by
    apply ObjectProperty.hom_ext
    ext E φ
    funext d
    change decide (X.obj.map d.op (i.hom.app E φ) ∈ Set.range (i.hom.app (op T))) = true
    apply decide_eq_true
    exact ⟨A.obj.map d.op φ, NatTrans.naturality_apply i.hom d.op φ⟩
  have hp : IsPullback i (hone.from A) χ truth := by
    apply IsPullback.of_map_of_faithful (IsDSpace K T).ι
    apply IsPullback.of_forall_isPullback_app
    intro E
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun f : A ⟶ Ω => f.hom.app E) w
    · intro a b hab
      exact subspace_component_injective i hsub E hab.1
    · intro φ z hz
      obtain ⟨ψ, hψ, _⟩ := hsub φ (by
        intro d
        have hd := congrFun hz d
        change decide (X.obj.map d.op φ ∈ Set.range (i.hom.app (op T))) = true at hd
        exact of_decide_eq_true hd)
      refine ⟨ψ, hψ, ?_⟩
      exact hT.hom_ext _ _
  refine ⟨χ, hp, ?_⟩
  intro χ' hp'
  have hpt := ((IsDSpace K T).ι.map_isPullback hp').app (op T)
  apply ObjectProperty.hom_ext
  ext E φ
  funext d
  apply Bool.eq_iff_iff.mpr
  change χ'.hom.app E φ d = true ↔
    decide (X.obj.map d.op φ ∈ Set.range (i.hom.app (op T))) = true
  rw [decide_eq_true_eq]
  have hn : χ'.hom.app (op T) (X.obj.map d.op φ) (𝟙 T) = χ'.hom.app E φ d := by
    have h := congrFun (NatTrans.naturality_apply χ'.hom d.op φ) (𝟙 T)
    change χ'.hom.app (op T) (X.obj.map d.op φ) (𝟙 T) =
      χ'.hom.app E φ ((𝟙 T) ≫ d) at h
    simpa only [Category.id_comp] using h
  constructor
  · intro ht
    have hfun : χ'.hom.app (op T) (X.obj.map d.op φ) = truth.hom.app (op T) (𝟙 T) := by
      funext e
      have he : e = 𝟙 T := hT.hom_ext _ _
      change χ'.hom.app (op T) (X.obj.map d.op φ) e = true
      rw [he, hn, ht]
    obtain ⟨a, ha, _⟩ := Types.exists_of_isPullback hpt (X.obj.map d.op φ) (𝟙 T) hfun
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    have h := congrArg (fun f : A ⟶ Ω => f.hom.app (op T) a (𝟙 T)) hp'.w
    change χ'.hom.app (op T) (i.hom.app (op T) a) (𝟙 T) = true at h
    rw [ha, hn] at h
    exact h
