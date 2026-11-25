-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.smoothOrderOneCentersIsolated_of_principalizationCertificate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:07.934461+00:00
-- url     : https://prove2.me/submissions/1ee01e52-43b7-4061-bbb4-c77ab29ef290

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_subset_support_of_agreeNear
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_false_of_smoothOrderOneCentersIsolated_opens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_false_of_isOpen_preimage_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_eq
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isClosed_preimage_subscheme__comp___f5c54755774e
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
private theorem orderAt_eq_one_of_agreeNear {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} (C : PointedIrreducibleClosed W)
    (hp : Smooth p)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    {x : ↥W} (hx : x ∈ C.S) : orderAt I x = 1 := by
  rw [hV.orderAt_congr W I (V W ⟨C.S, C.closedS⟩) x (hagree x hx)]
  exact hG.orderAt_vanishing_eq_one k W p hp ⟨C.S, C.closedS⟩ C.irredS hsm hcomp x hx
private theorem false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (N Z : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (H : (U.toScheme).IdealSheafData)
    (hptU : C.pt ∈ (U : Set ↥W))
    (hH : IsSmoothDivisor (U.ι ≫ p) H)
    (hNsubH : ((N.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hZH : ((Z.comap U.ι).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (J : Option ((H.subscheme).IdealSheafData))
    (hJnone : J = none →
      IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.ι).support : Set ↥(U.toScheme))))
    (hJcomp : ∀ Jz, J = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ Jz, J = some Jz → ∀ x : ↥(H.subscheme),
      (H.subschemeι ≫ U.ι).base x ∉ Mem →
      ∃ V' : (H.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.ι = ((N.comap U.ι).comap H.subschemeι).comap V'.ι)
    (ih : ∀ Jz, J = some Jz →
      SmoothOrderOneCentersIsolated V H.subscheme (H.subschemeι ≫ (U.ι ≫ p)) Jz μ
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) ((Z.comap U.ι).comap H.subschemeι))
    (hp : Smooth p) (hm : μ = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  have hxiS : C.xi ∈ C.S := C.genericXi.mem
  have hordxi : orderAt N C.xi = 1 :=
    orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagree hxiS
  have hxiN : C.xi ∈ (N.support : Set ↥W) :=
    (one_le_orderAt_iff_mem_support N C.xi).mp (le_of_eq hordxi.symm)
  cases hJ : J with
  | none =>
    exact false_of_isOpen_preimage_support hV W N Z
      ⟨C.S, C.S, C.xi, C.xi, C.pt, C.closedS, C.closedS, C.irredS, C.irredS, C.genericXi,
        C.genericXi, C.memPt, C.memPt⟩ U H hptU hpt hZH hNsubH (hJnone hJ) hxi hxiN
  | some Jz =>
    have hIH := ih Jz hJ
    have hxiU : C.xi ∈ (U : Set ↥W) :=
      (C.genericXi.mem_open_set_iff (hV.isOpen_opens W U)).mpr ⟨C.pt, C.memPt, hptU⟩
    have hCsubN : C.S ⊆ (N.support : Set ↥W) :=
      subset_support_of_agreeNear hV W N C.S C.closedS hagree
    have hsubH : (U.ι.base ⁻¹' C.S) ⊆ (H.support : Set ↥(U.toScheme)) := by
      intro y hy
      apply hNsubH
      rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
      exact hCsubN hy
    obtain ⟨y0, hy0⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.xi hxiU hxiS
    obtain ⟨y1, hy1⟩ := exists_subschemeι_comp_ι_apply_eq_of_mem hV W U H C.S hsubH C.pt hptU C.memPt
    have hS'closed : IsClosed ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isClosed_preimage_subschemeι_comp_ι hV W U H C.S C.closedS
    have hgen' : IsGenericPoint y0 ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) :=
      isGenericPoint_preimage_subschemeι_comp_ι hV W U H C.S C.xi C.genericXi y0 hy0
    have hirr' : IsIrreducible ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) := by
      rw [← hgen']
      exact isIrreducible_singleton.closure
    have hmemPt : y1 ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      show (H.subschemeι ≫ U.ι).base y1 ∈ C.S
      rw [hy1]
      exact C.memPt
    have hagree' : ∀ x ∈ (H.subschemeι ≫ U.ι).base ⁻¹' C.S,
        AgreeNear Jz (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x := by
      intro x hx
      have h1 : AgreeNear ((N.comap U.ι).comap H.subschemeι)
          (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x :=
        hV.agreeNear_vanishing_restrict W N U H ⟨C.S, C.closedS⟩
          ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ x rfl hsubH (hagree _ hx)
      have h2 : AgreeNear Jz ((N.comap U.ι).comap H.subschemeι) x :=
        hJloc Jz hJ x (Set.disjoint_left.mp hdisj hx)
      exact hV.agreeNear_trans H.subscheme Jz ((N.comap U.ι).comap H.subschemeι)
        (V H.subscheme ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩) x h2 h1
    have hS'J : ((H.subschemeι ≫ U.ι).base ⁻¹' C.S) ⊆ (Jz.support : Set ↥(H.subscheme)) :=
      subset_support_of_agreeNear hV H.subscheme Jz ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        hS'closed hagree'
    have hcomp' : ∀ E ∈ irreducibleComponents ↥(H.subscheme),
        ¬ E ⊆ (H.subschemeι ≫ U.ι).base ⁻¹' C.S := by
      intro E hE hEsub
      exact hV.not_subset_support_of_nonzeroOnComponents H.subscheme Jz (hJcomp Jz hJ) E hE
        (hEsub.trans hS'J)
    have hsupp : ∀ x : ↥(H.subscheme),
        x ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) ↔
          (H.subschemeι ≫ U.ι).base x ∈ (Z.support : Set ↥W) := by
      intro x
      constructor
      · intro hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at hx
          exact hx
        have h2 : (U.ι.base (H.subschemeι.base x)) ∈ (Z.support : Set ↥W) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at h1
          exact h1
        rw [hV.base_comp]
        exact h2
      · intro hx
        rw [hV.base_comp] at hx
        have h1 : (H.subschemeι.base x) ∈ ((Z.comap U.ι).support : Set ↥(U.toScheme)) := by
          rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
          exact hx
        rw [FunctorialResolution.EmbeddedResolution.support_comap_eq]
        exact h1
    have hxi' : y0 ∉ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      intro hmem
      apply hxi
      have h1 := (hsupp y0).mp hmem
      rw [hy0] at h1
      exact h1
    have hpt' : y1 ∈ ((((Z.comap U.ι).comap H.subschemeι)).support : Set ↥(H.subscheme)) := by
      refine (hsupp y1).mpr ?_
      rw [hy1]
      exact hpt
    have hdisj' : Disjoint ((H.subschemeι ≫ U.ι).base ⁻¹' C.S)
        ((H.subschemeι ≫ U.ι).base ⁻¹' Mem) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact (Set.disjoint_left.mp hdisj hx) hx2
    have hsmooth : Smooth (H.subschemeι ≫ (U.ι ≫ p)) :=
      ((isSmoothDivisor_iff (U.ι ≫ p) H).mp hH).2
    have hsmV : Smooth ((V H.subscheme
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩).subschemeι ≫
        (H.subschemeι ≫ (U.ι ≫ p))) :=
      hG.smooth_vanishing_hypersurface k W p U H hH ⟨C.S, C.closedS⟩
        ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, hS'closed⟩ rfl hsubH hsm
    exact hIH ⟨(H.subschemeι ≫ U.ι).base ⁻¹' C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
      hsmooth hm hsmV hcomp' hxi' hdisj' hagree' hpt'
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ => SmoothOrderOneCentersIsolated V W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => SmoothOrderOneCentersIsolated V W p N μ Mem Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p I m Mem Z hm2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p I m Mem Z M N μ hI hM hmu hZc hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hIN : ∀ x ∈ C.S, AgreeNear I N x := by
      intro x hx
      have hxM : x ∉ (M.support : Set ↥W) := fun hmm =>
        (Set.disjoint_left.mp hdisj hx) (hM hmm)
      obtain ⟨Uc, hUcx, hUcdisj⟩ :
          ∃ Uc : W.Opens, x ∈ Uc ∧ Disjoint ((Uc : Set ↥W)) (M.support : Set ↥W) :=
        ⟨⟨(M.support : Set ↥W)ᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hxM,
          disjoint_compl_left⟩
      refine ⟨Uc, hUcx, ?_⟩
      have hMtop : M.comap Uc.ι = ⊤ := FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint M Uc hUcdisj
      rw [hI, hV.comap_mul W Uc.toScheme Uc.ι M N, hMtop, hV.top_mul]
    have hagreeN : ∀ x ∈ C.S, AgreeNear N (V W ⟨C.S, C.closedS⟩) x := fun x hx =>
      hV.agreeNear_trans W N I (V W ⟨C.S, C.closedS⟩) x (agreeNear_symm (hIN x hx)) (hagree x hx)
    rcases Nat.lt_or_ge μ 2 with h2 | h2
    · have hmu1 : μ = 1 := by omega
      exact ih C hp hmu1 hsm hcomp hxi hdisj hagreeN hpt
    · have hord : orderAt N C.pt = 1 :=
        orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagreeN C.memPt
      have hmem : C.pt ∈ orderAtLeastLocus N μ := hZc hpt
      rw [FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff, hord] at hmem
      have hle : μ ≤ 1 := by exact_mod_cast hmem
      omega
  · intro W p I m Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p I Z m Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
    exact (Set.disjoint_left.mp hdisj C.memPt) (hZM hpt)
  · intro W p N μ Mem Z hmu2 C hp hm hsm hcomp hxi hdisj hagree hpt
    omega
  · intro W p N μ Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_smoothOrderOneCentersIsolated_opens hV hG p N Z μ Mem C (U C.pt hz) (hU C.pt hz)
      (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih C hp hm hsm hcomp hxi
      hdisj hagree hpt
    have hz : C.pt ∈ Z.support := hpt
    exact false_of_isSmoothDivisor_of_smoothOrderOneCentersIsolated hV hG p N Z μ Mem C (U C.pt hz) (H C.pt hz) (hU C.pt hz) (hH C.pt hz)
      (hNsubH C.pt hz) (hZH C.pt hz) (J C.pt hz) (hJnone C.pt hz) (hJcomp C.pt hz)
      (hJloc C.pt hz) (fun Jz hJ => ih C.pt hz Jz hJ) hp hm hsm hcomp hxi hdisj hagree hpt
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
