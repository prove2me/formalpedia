-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_iso_pullback_coprod_desc_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:39.842704+00:00
-- url     : https://prove2.me/submissions/02360095-9b6d-47a0-95e3-e7e63bb8da31

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FunctorialResolution.Blowup
private theorem range_opens_ι {X : Scheme.{u}} (U : X.Opens) :
    Set.range ⇑U.ι.base = (U : Set ↥X) := by
  simp
private theorem notMem_of_isCompl {X : Scheme.{u}} {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ (U : Set ↥X)) (hV : x ∈ (V : Set ↥X)) : False := by
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : ((U ⊓ V : X.Opens) : Set ↥X) = ((⊥ : X.Opens) : Set ↥X) := by rw [h1]
  have hd : (U : Set ↥X) ∩ (V : Set ↥X) = (∅ : Set ↥X) := by simpa using h2
  have hx : x ∈ (∅ : Set ↥X) := by
    rw [← hd]
    exact ⟨hU, hV⟩
  simp at hx
private theorem range_fst_subset_range_inr_of_isCompl {X A F : Scheme.{u}} (f : A ⟶ X)
    (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (s : PullbackCone (coprod.desc f g) V.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
  rintro ⟨a, ha⟩
  have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← base_comp_apply, ← base_comp_apply]
    exact hc
  have hd : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g = f := coprod.inl_desc f g
  have e2 : (coprod.desc f g).base ((coprod.inl : A ⟶ A ⨿ F).base a) = f.base a := by
    rw [← base_comp_apply, hd]
  have hfa : f.base a = V.ι.base ((PullbackCone.snd s).base t) := by
    rw [← e2, ha, e1]
  refine notMem_of_isCompl h (f.base a) ?_ ?_
  · rw [← range_opens_ι U]
    exact hf (Set.mem_range_self a)
  · rw [hfa, ← range_opens_ι V]
    exact Set.mem_range_self _
private theorem isPullback_inr_coprod_desc {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    IsPullback (coprod.inr : F ⟶ A ⨿ F) (IsOpenImmersion.lift V.ι g hg)
      (coprod.desc f g) V.ι := by
  have hinr : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g = g := coprod.inr_desc f g
  have hliftfac : IsOpenImmersion.lift V.ι g hg ≫ V.ι = g :=
    IsOpenImmersion.lift_fac V.ι g hg
  have hw : (coprod.inr : F ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift V.ι g hg ≫ V.ι := hinr.trans hliftfac.symm
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl f g h hf s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫
            IsOpenImmersion.lift V.ι g hg) ≫ V.ι
        = PullbackCone.snd s ≫ V.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : F ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ (coprod.inr : F ⟶ A ⨿ F) := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    ∃ e : pullback (coprod.desc f g) V.ι ≅ F,
      e.hom ≫ IsOpenImmersion.lift V.ι g hg
          = pullback.snd (coprod.desc f g) V.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) V.ι = (coprod.inr : F ⟶ A ⨿ F) := by
  have hpb := isPullback_inr_coprod_desc f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst
end FunctorialResolution.Blowup
