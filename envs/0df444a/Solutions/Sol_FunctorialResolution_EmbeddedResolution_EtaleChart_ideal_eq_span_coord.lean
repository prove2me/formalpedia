-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.ideal_eq_span_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:08.572657+00:00
-- url     : https://prove2.me/submissions/99b91675-0c13-4051-b71a-e89f9c1ea034

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_top_eq_map_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top
import Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem ideal_map_topIso_inv_injective {X₁ : Scheme.{u}} (V : X₁.Opens)
    {J₁ J₂ : Ideal Γ(X₁, V)}
    (hJ : Ideal.map V.topIso.inv.hom J₁ = Ideal.map V.topIso.inv.hom J₂) : J₁ = J₂ := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = RingHom.id _ := by
    ext x
    exact Iso.inv_hom_id_apply V.topIso x
  have key : ∀ J : Ideal Γ(X₁, V),
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [Ideal.map_map, hid, Ideal.map_id]
  rw [← key J₁, hJ, key J₂]
private theorem ι_appLE_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel X₁ _ _
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (I : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal I U = c.coordIdeal S) :
    I.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) := by
  have hUaff : IsAffine U.toScheme := hU
  have e : (⊤ : (U.toScheme).Opens) ≤ U.ι ⁻¹ᵁ U := by
    intro x _
    exact x.2
  have hL : (restrictIdeal I U).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩) := by
    rw [restrictIdeal_eq_comap_ι, ← ι_appLE_top_eq_topIso_inv U e]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U, hU⟩
      ⟨⊤, isAffineOpen_top U.toScheme⟩ e
  have hR : (c.coordIdeal S).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
      coordSubspaceIdeal_eq_ofIdealTop_span_coord, AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top,
      Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
    refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
    exact (Iso.hom_inv_id_apply U.topIso _).symm
  have hfin : Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩)
      = Ideal.map U.topIso.inv.hom (Ideal.span (c.coord '' (S : Set (Fin m)))) := by
    rw [← hL, ← hR, h]
  exact ideal_map_topIso_inv_injective U hfin
end EtaleChart
end FunctorialResolution.EmbeddedResolution
