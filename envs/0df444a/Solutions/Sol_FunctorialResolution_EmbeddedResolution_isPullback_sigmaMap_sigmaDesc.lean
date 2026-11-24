-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_sigmaMap_sigmaDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:07.042591+00:00
-- url     : https://prove2.me/submissions/f0b161bc-9f4e-4624-9dba-101d2c21297c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem isIso_sigmaDesc_of_isPullback {ι : Type u} [Finite ι] {P : Scheme.{u}}
    (B C : ι → Scheme.{u}) (f : P ⟶ ∐ B) (j : ∀ a, C a ⟶ B a) (u : ∀ a, C a ⟶ P)
    (hsq : ∀ a, IsPullback (u a) (j a) f (Sigma.ι B a)) : IsIso (Sigma.desc u) := by
  have e1 : (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as) ≫ (colimit.cocone (Discrete.functor B)).ι
      = (Cofan.mk P u).ι ≫ (Functor.const (Discrete ι)).map f := by
    apply NatTrans.ext
    funext x
    obtain ⟨a⟩ := x
    exact ((hsq a).w).symm
  have hpb : ∀ x : Discrete ι, IsPullback ((Cofan.mk P u).ι.app x)
      ((Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as).app x) f ((colimit.cocone (Discrete.functor B)).ι.app x) := by
    rintro ⟨a⟩
    exact hsq a
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (colimit.isColimit (Discrete.functor B)) (Cofan.mk P u)
      (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B) fun a => j a.as)
      f e1 (NatTrans.Equifibered.of_discrete _) hpb
  have key : Sigma.desc u
      = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor C)) hc').hom := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Discrete.functor C)) hc' ⟨a⟩).symm
  rw [key]
  infer_instance
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {ι : Type u} [Finite ι] {A Y : Scheme.{u}} (i : Y ⟶ A)
    (B C : ι → Scheme.{u}) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (Limits.Sigma.desc q) (Limits.Sigma.desc h) i := by
  have hcomm : ∀ a, (j a ≫ Sigma.ι B a) ≫ Sigma.desc h = q a ≫ i := by
    intro a
    rw [Category.assoc, Sigma.ι_desc]
    exact (hsq a).w
  obtain ⟨u, hufst, husnd⟩ : ∃ u : ∀ a, C a ⟶ pullback (Sigma.desc h) i,
      (∀ a, u a ≫ pullback.fst (Sigma.desc h) i = j a ≫ Sigma.ι B a) ∧
        (∀ a, u a ≫ pullback.snd (Sigma.desc h) i = q a) :=
    ⟨fun a => pullback.lift (j a ≫ Sigma.ι B a) (q a) (hcomm a),
      fun a => pullback.lift_fst _ _ _, fun a => pullback.lift_snd _ _ _⟩
  have hP : IsPullback (pullback.fst (Sigma.desc h) i) (pullback.snd (Sigma.desc h) i)
      (Sigma.desc h) i := IsPullback.of_hasPullback _ _
  have hsq2 : ∀ a, IsPullback (j a) (u a) (Sigma.ι B a) (pullback.fst (Sigma.desc h) i) := by
    intro a
    refine IsPullback.of_bot ?_ (hufst a).symm hP
    rw [husnd a, Sigma.ι_desc]
    exact hsq a
  have : IsIso (Sigma.desc u) :=
    isIso_sigmaDesc_of_isPullback B C (pullback.fst (Sigma.desc h) i) j u
      (fun a => (hsq2 a).flip)
  have hcs : CommSq (Limits.Sigma.map j) (Sigma.desc q) (Sigma.desc h) i := by
    constructor
    apply Sigma.hom_ext
    intro a
    simp [(hsq a).w]
  refine IsPullback.of_iso_pullback hcs (asIso (Sigma.desc u)) ?_ ?_
  · apply Sigma.hom_ext
    intro a
    simp [hufst a]
  · apply Sigma.hom_ext
    intro a
    simp [husnd a]
end FunctorialResolution.EmbeddedResolution
