-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.resLE_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:30:29.29954+00:00
-- url     : https://prove2.me/submissions/57d769f1-8dac-45cd-be83-ff1a06092469

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimensionPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace HasSmoothCoordCodim
variable {k : Type u} [Field k]
private theorem smooth_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f]
    (U : Y.Opens) : AlgebraicGeometry.Smooth (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth)
    (isPullback_morphismRestrict f U).flip ‹AlgebraicGeometry.Smooth f›
private theorem resLE_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  simp [Scheme.Hom.resLE_comp_ι]
private theorem ker_eq_comap_of_isPullback {X X' X'' X₂ : Scheme.{u}} {τ : X ⟶ X'} [IsClosedImmersion τ]
    {g : X'' ⟶ X'} {τ'' : X₂ ⟶ X''} {p : X₂ ⟶ X} (H : IsPullback p τ'' τ g) :
    τ''.ker = τ.ker.comap g := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion τ g, ← H.flip.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]
private theorem ker_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) :
    (f.resLE U (f ⁻¹ᵁ U) le_rfl).ker = f.ker.comap U.ι := by
  have H := (isPullback_morphismRestrict f U).flip
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact ker_eq_comap_of_isPullback H
end HasSmoothCoordCodim
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
theorem _root_.solution {X X' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (O : X'.Opens) :
    HasSmoothCoordCodim (O.ι ≫ s) (τ.resLE O (τ ⁻¹ᵁ O) le_rfl) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h ((τ ⁻¹ᵁ O).ι.base x)
  have : AlgebraicGeometry.Smooth q := hq
  have : AlgebraicGeometry.Smooth O.ι := inferInstance
  have : AlgebraicGeometry.Smooth (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := smooth_resLE O.ι U
  have hw : O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) = τ.base ((τ ⁻¹ᵁ O).ι.base x) :=
    congrArg (fun m : (τ ⁻¹ᵁ O).toScheme ⟶ X' => m.base x) (resLE_comp_ι τ O)
  refine ⟨O.ι ⁻¹ᵁ U, ?_, O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) ∈ U
    rw [hw]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι O.ι U, Category.assoc]
  · calc restrictIdeal (τ.resLE O (τ ⁻¹ᵁ O) le_rfl).ker (O.ι ⁻¹ᵁ U)
        = (τ.ker.comap O.ι).comap (O.ι ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_resLE]
      _ = τ.ker.comap ((O.ι ⁻¹ᵁ U).ι ≫ O.ι) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ U.ι) := by rw [resLE_comp_ι O.ι U]
      _ = (τ.ker.comap U.ι).comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
