-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:01:56.837225+00:00
-- url     : https://prove2.me/submissions/5aef17b9-4fa0-480d-b6fa-900912f854d9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_nonZeroDivisors
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
private theorem appLE_ι_top_eq_topIso_inv {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ hle = V.topIso.inv := by
  simp
  rfl
private theorem bijective_appLE_ι_top {Y : Scheme.{u}} (V : Y.Opens)
    (hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) := by
  rw [appLE_ι_top_eq_topIso_inv V hle]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective
private theorem ideal_eq_top_of_restrictIdeal_eq_top {Y : Scheme.{u}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := V.ι_preimage_self.ge
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ hle
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩) = ⊤ :=
    key.symm
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ hle)) (D.ideal ⟨V, hV⟩))
      = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact bijective_appLE_ι_top V hle
  rw [← hcomap, key2, Ideal.comap_top]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (D : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor D := by
  intro x
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨f, hf, hfspan⟩ :
      ∃ f : ↑(X.presheaf.obj (op V)), f ∈ nonZeroDivisors ↑(X.presheaf.obj (op V)) ∧
        D.ideal ⟨V, hV⟩ = Ideal.span {f} := by
    rcases hc with htop | ⟨j, hj⟩
    · refine ⟨1, one_mem _, ?_⟩
      rw [ideal_eq_top_of_restrictIdeal_eq_top D hV (restrictIdeal_eq_top_of_le D hVU htop),
        Ideal.span_singleton_one]
    · refine ⟨(c.restrict hVU).coord j, coord_mem_nonZeroDivisors hV (c.restrict hVU) j, ?_⟩
      rw [(c.restrict hVU).ideal_eq_span_coord hV D {j}
        (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hj), Finset.coe_singleton,
        Set.image_singleton]
  exact ⟨⟨V, hV⟩, f, hxV, hf, hfspan⟩
end FunctorialResolution.EmbeddedResolution
