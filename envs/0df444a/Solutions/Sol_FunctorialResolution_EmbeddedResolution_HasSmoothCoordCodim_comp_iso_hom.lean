-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.comp_iso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:38.530525+00:00
-- url     : https://prove2.me/submissions/3cd5c6c4-3a04-4cb7-ad5a-4199a2b3973d

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
private theorem ker_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (φ : Y ≅ Z) :
    (f ≫ φ.hom).ker = f.ker.comap φ.inv :=
  ker_eq_comap_of_isPullback (p := 𝟙 X) (IsPullback.of_horiz_isIso ⟨by simp⟩)
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
theorem _root_.solution {X X' X'' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (φ : X' ≅ X'')
    (s' : X'' ⟶ Spec (CommRingCat.of k)) (hφ : φ.hom ≫ s' = s) :
    HasSmoothCoordCodim s' (τ ≫ φ.hom) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h x
  have : AlgebraicGeometry.Smooth q := hq
  have : AlgebraicGeometry.Smooth φ.inv := inferInstance
  have : AlgebraicGeometry.Smooth (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := smooth_resLE φ.inv U
  have hs' : φ.inv ≫ s = s' := by rw [← hφ, Iso.inv_hom_id_assoc]
  refine ⟨φ.inv ⁻¹ᵁ U, ?_, φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show φ.inv.base ((τ ≫ φ.hom).base x) ∈ U
    have hb : φ.inv.base ((τ ≫ φ.hom).base x) = τ.base x :=
      congrArg (fun m : X ⟶ X' => m.base x) (by simp : (τ ≫ φ.hom) ≫ φ.inv = τ)
    rw [hb]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι φ.inv U, Category.assoc, hs']
  · calc restrictIdeal (τ ≫ φ.hom).ker (φ.inv ⁻¹ᵁ U)
        = (τ.ker.comap φ.inv).comap (φ.inv ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_comp_iso]
      _ = τ.ker.comap ((φ.inv ⁻¹ᵁ U).ι ≫ φ.inv) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ U.ι) := by
          rw [resLE_comp_ι φ.inv U]
      _ = (τ.ker.comap U.ι).comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
