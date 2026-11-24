-- Prove2me | solution 1 for Formalism.HN.degree_supermodular_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:02.664929+00:00
-- url     : https://prove2.me/submissions/b321528f-a609-4d3a-b036-0441fd5774f8

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Theorems.Thm_Formalism_RankSupermodularCovolume_rk_sup_add_rk_inf
import Theorems.Thm_Formalism_RankSupermodularCovolume_mem_span_inf_of_mem_span
import Theorems.Thm_Formalism_RankSupermodularCovolume_covol_eq_relIndex_mul_covol
import Theorems.Thm_Formalism_RankSupermodularCovolume_orthogonal_starProjection_comp_of_le
import Theorems.Thm_Formalism_RankSupermodularCovolume_mem_of_orthogonal_starProjection_eq_zero
import Theorems.Thm_Formalism_RankSupermodularCovolume_covol_le_of_contraction
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_F_deg_eq_deg_add_deg_quot
import Theorems.Thm_Formalism_F_saturProps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open Formalism.F Formalism.RankSupermodularCovolume
namespace Formalism.HN
theorem _root_.solution : DegSupermodZ := by
  intro E _ _ _ L A B hL hA hB
  haveI := hL
  refine ⟨rk_sup_add_rk_inf L A B hA hB, ?_⟩
  have dsc : ∀ N : Submodule ℤ E, N ≤ L → DiscreteTopology N := fun N h =>
    DiscreteTopology.of_subset (s := (L : Set E)) ‹_› h
  have hSL : A ⊔ B ≤ L := sup_le hA hB
  haveI := dsc _ hSL
  haveI := dsc A hA
  haveI := dsc B hB
  haveI := dsc (A ⊓ B) (inf_le_left.trans hA)
  obtain ⟨hAsSat, hAAs, hrkAs⟩ := saturProps E (A ⊔ B) A ‹_› le_sup_left
  obtain ⟨hBsSat, hCBs, hrkBs⟩ := saturProps E B (A ⊓ B) ‹_› inf_le_right
  haveI := dsc (satur (A ⊔ B) A) (inf_le_left.trans hSL)
  haveI := dsc (satur B (A ⊓ B)) (inf_le_left.trans hB)
  obtain ⟨hqS, -, -⟩ := degQuot E (A ⊔ B) (satur (A ⊔ B) A) ‹_› hAsSat
  obtain ⟨hqB, -, -⟩ := degQuot E B (satur B (A ⊓ B)) ‹_› hBsSat
  haveI := hqS
  haveI := hqB
  have hdS := deg_eq_deg_add_deg_quot hAsSat
  have hdB := deg_eq_deg_add_deg_quot hBsSat

  have hAs_span : ∀ x ∈ satur (A ⊔ B) A, x ∈ span ℝ (A : Set E) := fun x hx =>
    (Submodule.mem_inf.1 hx).2
  have hBs_span : ∀ x ∈ satur B (A ⊓ B), x ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E) :=
    fun x hx => (Submodule.mem_inf.1 hx).2
  have hBsAs : satur B (A ⊓ B) ≤ satur (A ⊔ B) A := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨(le_sup_right : B ≤ A ⊔ B) (Submodule.mem_inf.1 hx).1, ?_⟩
    exact span_mono (fun y hy => (Submodule.mem_inf.1 hy).1) (hBs_span x hx)

  have hcA := covol_eq_relIndex_mul_covol A (satur (A ⊔ B) A) hAAs hrkAs.symm
  have hcC := covol_eq_relIndex_mul_covol (A ⊓ B) (satur B (A ⊓ B)) hCBs hrkBs.symm
  have hiA : A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup ≠ 0 := by
    intro h0
    have := covol_pos A
    rw [hcA, h0] at this
    simp at this
  have hiC : (A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup =
      A.toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup := by
    unfold AddSubgroup.relIndex
    congr 1
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hxB : (x : E) ∈ B := (Submodule.mem_inf.1 x.2).1
    exact ⟨fun h => (Submodule.mem_inf.1 h).1, fun h => Submodule.mem_inf.2 ⟨h, hxB⟩⟩
  have hle : (A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup ≤
      A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup := by
    rw [hiC]
    exact AddSubgroup.relIndex_le_of_le_right hBsAs hiA
  have hii : covol (satur (A ⊔ B) A) * covol (A ⊓ B) ≤ covol A * covol (satur B (A ⊓ B)) := by
    rw [hcA, hcC]
    have h1 := covol_pos (satur (A ⊔ B) A)
    have h2 := covol_pos (satur B (A ⊓ B))
    have h3 : ((A ⊓ B).toAddSubgroup.relIndex (satur B (A ⊓ B)).toAddSubgroup : ℝ) ≤
        (A.toAddSubgroup.relIndex (satur (A ⊔ B) A).toAddSubgroup : ℝ) := by exact_mod_cast hle
    have h4 := mul_le_mul_of_nonneg_right h3 (mul_pos h1 h2).le
    nlinarith [h4]

  have hspan : span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E) ≤
      span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E) := span_mono hBsAs
  have hPW0 : ∀ y ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E),
      (span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E))ᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact span_mono hCBs hy
  have hPU0 : ∀ y ∈ A, (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    exact subset_span (hAAs hy)
  have hmaps : ∀ x ∈ quot B (satur B (A ⊓ B)),
      (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x ∈
        quot (A ⊔ B) (satur (A ⊔ B) A) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨b, (le_sup_right : B ≤ A ⊔ B) hb, ?_⟩
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe]
    exact (orthogonal_starProjection_comp_of_le hspan b).symm
  let g : quot B (satur B (A ⊓ B)) →ₗ[ℤ] quot (A ⊔ B) (satur (A ⊔ B) A) :=
    (((span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ).restrict
      hmaps
  have hg : ∀ x, ((g x : quot (A ⊔ B) (satur (A ⊔ B) A)) : E) =
      (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x := fun x => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection x = 0 := by
      rw [← hg, hx]; rfl
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 x.2
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe] at hbx
    rw [← hbx, orthogonal_starProjection_comp_of_le hspan] at hx0
    have hbU := mem_of_orthogonal_starProjection_eq_zero hx0
    have hbA : b ∈ span ℝ (A : Set E) :=
      span_le.2 (fun y hy => hAs_span y hy) hbU
    have hbC := mem_span_inf_of_mem_span L A B hA hB hb hbA
    apply Subtype.ext
    rw [← hbx, hPW0 b hbC]
    rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
    have hpb : (span ℝ ((satur B (A ⊓ B) : Submodule ℤ E) : Set E))ᗮ.starProjection b ∈
        quot B (satur B (A ⊓ B)) := Submodule.mem_map.2 ⟨b, hb, rfl⟩
    refine ⟨⟨_, hpb⟩, Subtype.ext ?_⟩
    rw [hg]
    simp only [LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe, map_add, hPU0 a ha,
      zero_add]
    exact orthogonal_starProjection_comp_of_le hspan b
  let φ := LinearEquiv.ofBijective g ⟨hinj, hsurj⟩
  have hcov : covol (quot (A ⊔ B) (satur (A ⊔ B) A)) ≤ covol (quot B (satur B (A ⊓ B))) := by
    refine covol_le_of_contraction _ _ φ
      ((span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.starProjection) (fun x => hg x) ?_
    intro v
    first
      | exact Submodule.norm_starProjection_apply_le _ v
      | exact (span ℝ ((satur (A ⊔ B) A : Submodule ℤ E) : Set E))ᗮ.norm_starProjection_apply_le v
      | exact ContinuousLinearMap.le_of_opNorm_le _ (Submodule.starProjection_norm_le _) v
      | simpa using ContinuousLinearMap.le_of_opNorm_le _ (Submodule.starProjection_norm_le _) v
  have k1 : Real.log (covol (quot (A ⊔ B) (satur (A ⊔ B) A))) ≤
      Real.log (covol (quot B (satur B (A ⊓ B)))) :=
    Real.log_le_log (covol_pos _) hcov
  have k2 : Real.log (covol (satur (A ⊔ B) A)) + Real.log (covol (A ⊓ B)) ≤
      Real.log (covol A) + Real.log (covol (satur B (A ⊓ B))) := by
    rw [← Real.log_mul (covol_pos _).ne' (covol_pos _).ne',
      ← Real.log_mul (covol_pos _).ne' (covol_pos _).ne']
    exact Real.log_le_log (mul_pos (covol_pos _) (covol_pos _)) hii
  rw [hdS, hdB]
  unfold Formalism.F.deg
  linarith
end Formalism.HN
