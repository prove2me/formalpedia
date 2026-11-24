-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:22.954925+00:00
-- url     : https://prove2.me/submissions/abe987cf-adbf-4a24-b19b-7d9bbca0665a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
private theorem le_of_forall_ideal_le {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (H : ∀ U : Y.affineOpens, I.ideal U ≤ J.ideal U) : I ≤ J := H
private theorem mul_ideal_le_mul_ideal {Y : Scheme.{u}} {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) :
    F.ideal W * J.ideal W ≤ F.ideal W * J'.ideal W := h W
private theorem exists_affineOpen_ideal_eq_span_singleton {Y : Scheme.{u}} {F : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (x : Y) :
    ∃ (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens))), x ∈ (W : Y.Opens) ∧
      t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens)) ∧ F.ideal W = Ideal.span {t} := by
  unfold Blowup.IsLocallyGeneratedByNonZeroDivisor at hF
  exact hF x
private theorem ideal_le_ideal_of_mul_le_mul {Y : Scheme.{u}} {F J J' : Y.IdealSheafData}
    (h : F * J ≤ F * J') (W : Y.affineOpens) (t : Γ(Y, (W : Y.Opens)))
    (hFW : F.ideal W = Ideal.span {t}) (ht : t ∈ nonZeroDivisors Γ(Y, (W : Y.Opens))) :
    J.ideal W ≤ J'.ideal W := by
  intro b hb
  have h1 : t * b ∈ F.ideal W * J.ideal W := by
    rw [hFW]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) hb
  have h2 : t * b ∈ F.ideal W * J'.ideal W := mul_ideal_le_mul_ideal h W h1
  rw [hFW, Ideal.mem_span_singleton_mul] at h2
  obtain ⟨j, hj, hje⟩ := h2
  have h3 : (b - j) * t = 0 := by
    rw [sub_mul, mul_comm b t, mul_comm j t, hje, sub_self]
  have h4 : b = j := eq_of_sub_eq_zero ((mem_nonZeroDivisors_iff.mp ht).2 (b - j) h3)
  rw [h4]
  exact hj
private theorem span_eq_top_of_forall_exists_mem_basicOpen {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(Y, U))
    (h : ∀ x : Y, x ∈ U → ∃ f : s, x ∈ Y.basicOpen (f : Γ(Y, U))) :
    Ideal.span s = ⊤ := by
  rw [← IsAffineOpen.self_le_iSup_basicOpen_iff hU]
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (h x hx)
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
theorem _root_.solution {F J J' : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * J ≤ F * J') : J ≤ J' := by
  refine EmbeddedResolution.le_of_forall_ideal_le fun U => ?_
  intro b hb
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have hcover :
      Ideal.span {g : Γ(Y, (U : Y.Opens)) | ∃ n : ℕ, g ^ n * b ∈ J'.ideal U} = ⊤ := by
    refine EmbeddedResolution.span_eq_top_of_forall_exists_mem_basicOpen hU _ ?_
    intro x hx
    obtain ⟨V, t, hxV, htz, hFt⟩ := EmbeddedResolution.exists_affineOpen_ideal_eq_span_singleton hF x
    have hxUV : x ∈ (U : Y.Opens) ⊓ (V : Y.Opens) := ⟨hx, hxV⟩
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU V.2 x hxUV
    have hWfg : Y.affineBasicOpen f = Y.affineBasicOpen g := Subtype.ext hfg
    have hcan : J.ideal (Y.affineBasicOpen f) ≤ J'.ideal (Y.affineBasicOpen f) := by
      rw [hWfg]
      refine EmbeddedResolution.ideal_le_ideal_of_mul_le_mul h (Y.affineBasicOpen g)
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom t) ?_ ?_
      · rw [← F.map_ideal_basicOpen V g, hFt, Ideal.map_span, Set.image_singleton]
        rfl
      · have := V.2.isLocalization_basicOpen g
        exact IsLocalization.nonZeroDivisors_le_comap (.powers g) Γ(Y, Y.basicOpen g) htz
    have hbW : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ J.ideal (Y.affineBasicOpen f) := by
      rw [← J.map_ideal_basicOpen U f]
      exact Ideal.mem_map_of_mem _ hb
    have hbW2 : (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom b
        ∈ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J'.ideal U) := by
      have hbW3 := hcan hbW
      rwa [← J'.map_ideal_basicOpen U f] at hbW3
    have := hU.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ :=
      EmbeddedResolution.exists_pow_mul_mem_of_algebraMap_mem_map (S := Γ(Y, Y.basicOpen f)) f (J'.ideal U) b hbW2
    exact ⟨⟨f, n, hn⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J'.ideal U) _ hcover b ?_
  intro r
  have hr : ∃ n : ℕ, (r : Γ(Y, (U : Y.Opens))) ^ n * b ∈ J'.ideal U := r.2
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
