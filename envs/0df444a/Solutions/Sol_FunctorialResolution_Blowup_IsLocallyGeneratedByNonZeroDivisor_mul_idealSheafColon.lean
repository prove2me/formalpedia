-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.mul_idealSheafColon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:48.14202+00:00
-- url     : https://prove2.me/submissions/3773334e-2a40-483d-98a5-5cbf374c4ab3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
private theorem mul_ideal_apply {Y' : Scheme.{u}} (F G : Y'.IdealSheafData)
    (U : Y'.affineOpens) : (F * G).ideal U = F.ideal U * G.ideal U := rfl
private theorem span_eq_top_of_forall_exists_mem_basicOpen {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(Y, U))
    (h : ∀ x : Y, x ∈ U → ∃ f : s, x ∈ Y.basicOpen (f : Γ(Y, U))) :
    Ideal.span s = ⊤ := by
  rw [← IsAffineOpen.self_le_iSup_basicOpen_iff hU]
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (h x hx)
private theorem span_singleton_mul_colon {R : Type*} [CommRing R] {P J : Ideal R}
    (hP : ∃ f : R, P = Ideal.span {f}) (hJ : J ≤ P) : P * J.colon P = J := by
  obtain ⟨f, rfl⟩ := hP
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hJ hy)
    have hc : c ∈ J.colon (Ideal.span {f}) := by
      refine Submodule.mem_colon.2 ?_
      intro p hp
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [smul_eq_mul]
      have hre : c * (d * f) = d * (c * f) := by ring
      rw [hre]
      exact J.mul_mem_left d hy
    have hmem := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hc
    rwa [mul_comm f c] at hmem
private theorem exists_ideal_eq_span_singleton_congr {Y' : Scheme.{u}} (F : Y'.IdealSheafData)
    {W W' : Y'.affineOpens} (hW : W = W')
    (h : ∃ f : Γ(Y', W'), F.ideal W' = Ideal.span {f}) :
    ∃ f : Γ(Y', W), F.ideal W = Ideal.span {f} := by
  subst hW
  exact h
private theorem exists_basicOpen_ideal_eq_span_singleton {Y' : Scheme.{u}} (F : Y'.IdealSheafData)
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y'.affineOpens) (y : Y')
    (hy : y ∈ (U : Y'.Opens)) :
    ∃ g : Γ(Y', U), y ∈ Y'.basicOpen g ∧
      ∃ f : Γ(Y', Y'.affineBasicOpen g), F.ideal (Y'.affineBasicOpen g) = Ideal.span {f} := by
  obtain ⟨V, fV, hyV, hfV, hFV⟩ := hF y
  obtain ⟨g, h, heq, hyg⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
  refine ⟨g, hyg, ?_⟩
  have habo : Y'.affineBasicOpen g = Y'.affineBasicOpen h := Subtype.ext heq
  refine exists_ideal_eq_span_singleton_congr F habo ?_
  have hmap := F.map_ideal_basicOpen V h
  rw [hFV, Ideal.map_span, Set.image_singleton] at hmap
  exact ⟨_, hmap.symm⟩
private theorem span_eq_top_of_cover_basicOpen {Y' : Scheme.{u}} (U : Y'.affineOpens)
    (T : Set Γ(Y', U))
    (hcov : ∀ y : Y', y ∈ (U : Y'.Opens) → ∃ g ∈ T, y ∈ Y'.basicOpen g) :
    Ideal.span T = ⊤ := by
  refine span_eq_top_of_forall_exists_mem_basicOpen U.2 T ?_
  intro y hy
  obtain ⟨g, hgT, hyg⟩ := hcov y hy
  exact ⟨⟨g, hgT⟩, hyg⟩
private theorem exists_pow_mul_mem_mul_colon {Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (F I' : Y'.IdealSheafData) (hIle : ∀ U : Y'.affineOpens, I'.ideal U ≤ F.ideal U)
    (U : Y'.affineOpens) (x : Γ(Y', U)) (hx : x ∈ I'.ideal U) (g : Γ(Y', U))
    (f : Γ(Y', Y'.affineBasicOpen g))
    (hf : F.ideal (Y'.affineBasicOpen g) = Ideal.span {f}) :
    ∃ n : ℕ, g ^ n * x ∈ F.ideal U * (I'.ideal U).colon (F.ideal U) := by
  have : IsLocalization.Away g Γ(Y', Y'.basicOpen g) := U.2.isLocalization_basicOpen g
  have h1 : Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
      (F.ideal U * (I'.ideal U).colon (F.ideal U)) = I'.ideal (Y'.affineBasicOpen g) := by
    rw [Ideal.map_mul, F.map_ideal_basicOpen U g,
      idealSheafColon_ideal_map_basicOpen I' F U g]
    exact span_singleton_mul_colon ⟨f, hf⟩ (hIle (Y'.affineBasicOpen g))
  have h2 : (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op)) x ∈
      Ideal.map (CommRingCat.Hom.hom (Y'.presheaf.map (homOfLE (Y'.basicOpen_le g)).op))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := by
    rw [h1, ← I'.map_ideal_basicOpen U g]
    exact Ideal.mem_map_of_mem _ hx
  have h3 : algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g) x ∈
      Ideal.map (algebraMap Γ(Y', U) Γ(Y', Y'.basicOpen g))
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := h2
  exact exists_pow_mul_mem_of_algebraMap_mem_map g _ x h3
variable {X X₁ : Scheme.{u}}
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution [IsLocallyNoetherian Y]
    {F I' : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    F * EmbeddedResolution.idealSheafColon I' F = I' := by
  have hIle : ∀ U : Y.affineOpens, I'.ideal U ≤ F.ideal U := fun U => hI U
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro U
  rw [EmbeddedResolution.mul_ideal_apply, EmbeddedResolution.idealSheafColon_ideal]
  refine le_antisymm ?_ ?_
  · rw [Ideal.mul_le]
    intro a ha b hb
    have hb' := Submodule.mem_colon.mp hb a ha
    rw [smul_eq_mul] at hb'
    rw [mul_comm a b]
    exact hb'
  · intro x hx
    have hspan : Ideal.span {g : Γ(Y, U) | ∃ f : Γ(Y, Y.affineBasicOpen g),
        F.ideal (Y.affineBasicOpen g) = Ideal.span {f}} = ⊤ := by
      refine EmbeddedResolution.span_eq_top_of_cover_basicOpen U _ ?_
      intro y hy
      obtain ⟨g, hyg, hfg⟩ := EmbeddedResolution.exists_basicOpen_ideal_eq_span_singleton F hF U y hy
      exact ⟨g, hfg, hyg⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hspan x ?_
    intro r
    have hr : ∃ f : Γ(Y, Y.affineBasicOpen (r : Γ(Y, U))),
        F.ideal (Y.affineBasicOpen (r : Γ(Y, U))) = Ideal.span {f} := r.2
    obtain ⟨f, hf⟩ := hr
    obtain ⟨n, hn⟩ := EmbeddedResolution.exists_pow_mul_mem_mul_colon F I' hIle U x hx (r : Γ(Y, U)) f hf
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
