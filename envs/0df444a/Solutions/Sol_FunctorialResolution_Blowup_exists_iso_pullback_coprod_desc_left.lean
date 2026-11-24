-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_iso_pullback_coprod_desc_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:39.178987+00:00
-- url     : https://prove2.me/submissions/5f342fd7-e915-45b6-8225-7cda215b9bbd

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
private theorem range_ι_disjoint {X : Scheme.{u}} {U V : X.Opens} (h : IsCompl U V)
    (x : ↥X) (hU : x ∈ Set.range ⇑U.ι.base) (hV : x ∈ Set.range ⇑V.ι.base) : False := by
  rw [Scheme.Opens.range_ι] at hU
  rw [Scheme.Opens.range_ι] at hV
  have h1 : U ⊓ V = ⊥ := h.inf_eq_bot
  have h2 : x ∈ ((U ⊓ V : X.Opens) : Set ↥X) := by
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
    exact ⟨hU, hV⟩
  rw [h1] at h2
  simp at h2
private theorem range_fst_subset_range_inl_of_isCompl {X A F : Scheme.{u}} (f : A ⟶ X)
    (g : F ⟶ X) {U V : X.Opens} (h : IsCompl U V)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base)
    (s : PullbackCone (coprod.desc f g) U.ι) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
    rw [range_coprod_inr_eq_compl A F, Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.desc f g).base ((PullbackCone.fst s).base t)
      = U.ι.base ((PullbackCone.snd s).base t) := by
    have hc := congrArg (fun m : s.pt ⟶ X => m.base t) s.condition
    simpa using hc
  have e2 : (coprod.desc f g).base ((coprod.inr : F ⟶ A ⨿ F).base b) = g.base b := by
    rw [← base_comp_apply, coprod.inr_desc]
  have hfin : U.ι.base ((PullbackCone.snd s).base t) = g.base b := by
    rw [← e1, ← hb]
    exact e2
  have hmemV : U.ι.base ((PullbackCone.snd s).base t) ∈ Set.range ⇑V.ι.base := by
    rw [hfin]
    exact hg (Set.mem_range_self b)
  exact range_ι_disjoint h (U.ι.base ((PullbackCone.snd s).base t))
    (Set.mem_range_self _) hmemV
private theorem isPullback_inl_coprod_desc {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    IsPullback (coprod.inl : A ⟶ A ⨿ F) (IsOpenImmersion.lift U.ι f hf)
      (coprod.desc f g) U.ι := by
  have hw : (coprod.inl : A ⟶ A ⨿ F) ≫ coprod.desc f g
      = IsOpenImmersion.lift U.ι f hf ≫ U.ι := by
    rw [coprod.inl_desc, IsOpenImmersion.lift_fac]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl f g h hg s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫
            IsOpenImmersion.lift U.ι f hf) ≫ U.ι
        = PullbackCone.snd s ≫ U.ι := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
        (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F)
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A ⟶ A ⨿ F)
        = IsOpenImmersion.lift (coprod.inl : A ⟶ A ⨿ F) (PullbackCone.fst s)
            (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ (coprod.inl : A ⟶ A ⨿ F) := by
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
    ∃ e : pullback (coprod.desc f g) U.ι ≅ A,
      e.hom ≫ IsOpenImmersion.lift U.ι f hf
          = pullback.snd (coprod.desc f g) U.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) U.ι = (coprod.inl : A ⟶ A ⨿ F) := by
  have hpb := isPullback_inl_coprod_desc f g h hf hg
  refine ⟨hpb.isoPullback.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact hpb.isoPullback_hom_snd.symm
  · rw [Iso.symm_inv]
    exact hpb.isoPullback_hom_fst
end FunctorialResolution.Blowup
