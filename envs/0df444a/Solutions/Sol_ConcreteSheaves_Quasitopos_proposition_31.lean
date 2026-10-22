-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_31
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:18:40.977992+00:00
-- url     : https://prove2.me/submissions/ba89330b-d395-482c-a1b2-87d5fa647d16

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

namespace CS31Aux

lemma yoneda_dspace (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (X : D) : IsDSpace K T (yoneda.obj X) := by
  refine ⟨hK.subcanonical X, ?_⟩
  intro E φ ψ h
  apply hK.faithful
  intro x
  have := congrFun h x
  simpa using this

lemma omega_map {T : D} {X Y : D} (g : Y ⟶ X) (φ : (omegaPresheaf T).obj (op X)) :
    (omegaPresheaf T).map g.op φ = fun d => φ (d ≫ g) := rfl

lemma omega_dspace (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    IsDSpace K T (omegaPresheaf T) := by
  refine ⟨?_, ?_⟩
  · intro E R hR x hx
    have key : ∀ {Y1 : D} (f1 : Y1 ⟶ E) (h1 : R f1) (a : T ⟶ Y1)
        {Y2 : D} (f2 : Y2 ⟶ E) (h2 : R f2) (b : T ⟶ Y2), a ≫ f1 = b ≫ f2 →
        (x f1 h1 : (T ⟶ Y1) → Bool) a = (x f2 h2 : (T ⟶ Y2) → Bool) b := by
      intro Y1 f1 h1 a Y2 f2 h2 b hab
      have := congrFun (hx a b h1 h2 hab) (𝟙 T)
      rw [omega_map, omega_map] at this
      simpa using this
    choose Y f hf y hy using hK.jointlySurj R hR
    let t : (omegaPresheaf T).obj (op E) := fun d => (x (f d) (hf d) : (T ⟶ Y d) → Bool) (y d)
    refine ⟨t, ?_, ?_⟩
    · intro Z g hg
      rw [omega_map]
      funext d'
      exact key _ _ _ g hg d' (by rw [hy])
    · intro t' ht'
      funext d
      have e := congrFun (ht' (f d) (hf d)) (y d)
      rw [omega_map] at e
      change (t' : (T ⟶ E) → Bool) (y d ≫ f d) = _ at e
      rw [hy] at e
      exact e
  · intro E φ ψ h
    funext d
    have := congrFun (congrFun h d) (𝟙 T)
    change (φ : (T ⟶ E) → Bool) (𝟙 T ≫ d) = (ψ : (T ⟶ E) → Bool) (𝟙 T ≫ d) at this
    simpa using this

/-- The characteristic map of a set of points. -/
noncomputable def chi (T : D) (Y : Dᵒᵖ ⥤ Type u) (S : Set (Y.obj (op T))) :
    Y ⟶ omegaPresheaf T where
  app := fun E => ↾(fun φ => fun d : T ⟶ E.unop =>
    @decide (Y.map d.op φ ∈ S) (Classical.propDecidable _))
  naturality := by
    intro E E' u
    ext φ
    funext d
    show @decide (Y.map d.op (Y.map u φ) ∈ S) (Classical.propDecidable _) =
      @decide (Y.map (d ≫ u.unop).op φ ∈ S) (Classical.propDecidable _)
    rw [← FunctorToTypes.map_comp_apply]
    rfl

end CS31Aux

open CS31Aux

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {X Y : DSpace K T} (f : X ⟶ Y) :
    (Mono f ↔ Function.Injective (f.hom.app (op T))) ∧
      (Epi f ↔ Function.Surjective (f.hom.app (op T))) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hf x y hxy
    let yT : DSpace K T := ⟨yoneda.obj T, yoneda_dspace K T hT hK T⟩
    let gx : yT ⟶ X := ObjectProperty.homMk (yonedaEquiv.symm x)
    let gy : yT ⟶ X := ObjectProperty.homMk (yonedaEquiv.symm y)
    have hc : gx ≫ f = gy ≫ f := by
      apply InducedCategory.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simpa [gx, gy] using hxy
    have := congrArg (fun g : yT ⟶ X => yonedaEquiv g.hom) (hf.right_cancellation _ _ hc)
    simpa [gx, gy] using this
  · intro hinj
    constructor
    intro Z g1 g2 h
    apply InducedCategory.hom_ext
    ext E φ
    apply X.property.2 E.unop
    funext d
    show X.obj.map d.op (g1.hom.app E φ) = X.obj.map d.op (g2.hom.app E φ)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    apply hinj
    have := congrArg (fun g : Z ⟶ Y => g.hom.app (op T) (Z.obj.map d.op φ)) h
    simpa using this
  · intro hf y
    let Ω : DSpace K T := ⟨omegaPresheaf T, omega_dspace K T hT hK⟩
    let c1 : Y ⟶ Ω := ObjectProperty.homMk (chi T Y.obj (Set.range (f.hom.app (op T))))
    let c2 : Y ⟶ Ω := ObjectProperty.homMk (chi T Y.obj Set.univ)
    have hc : f ≫ c1 = f ≫ c2 := by
      apply InducedCategory.hom_ext
      ext E φ
      funext d
      show @decide (Y.obj.map d.op (f.hom.app E φ) ∈ Set.range (f.hom.app (op T)))
          (Classical.propDecidable _) =
        @decide (Y.obj.map d.op (f.hom.app E φ) ∈ (Set.univ : Set (Y.obj.obj (op T))))
          (Classical.propDecidable _)
      simp only [Set.mem_univ, decide_true, decide_eq_true_eq]
      exact ⟨_, NatTrans.naturality_apply f.hom d.op φ⟩
    have := congrFun (congrArg (fun g : Y ⟶ Ω => (g.hom.app (op T) y : (T ⟶ T) → Bool))
      (hf.left_cancellation _ _ hc)) (𝟙 T)
    simp only [c1, c2, ObjectProperty.homMk_hom] at this
    change @decide (Y.obj.map (𝟙 T).op y ∈ Set.range (f.hom.app (op T)))
        (Classical.propDecidable _) =
      @decide (Y.obj.map (𝟙 T).op y ∈ (Set.univ : Set (Y.obj.obj (op T))))
        (Classical.propDecidable _) at this
    simpa using this
  · intro hsurj
    constructor
    intro Z g1 g2 h
    apply InducedCategory.hom_ext
    ext E φ
    apply Z.property.2 E.unop
    funext d
    show Z.obj.map d.op (g1.hom.app E φ) = Z.obj.map d.op (g2.hom.app E φ)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    obtain ⟨x, hx⟩ := hsurj (Y.obj.map d.op φ)
    rw [← hx]
    have := congrArg (fun g : X ⟶ Z => g.hom.app (op T) x) h
    simpa using this
