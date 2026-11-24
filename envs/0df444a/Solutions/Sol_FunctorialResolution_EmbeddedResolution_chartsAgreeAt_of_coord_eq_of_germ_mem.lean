-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartsAgreeAt_of_coord_eq_of_germ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:56.314191+00:00
-- url     : https://prove2.me/submissions/97ebb2ad-a72b-4893-967e-f1e3eb535af4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactChartUniqueness
import Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartsAgreeAt_of_germ_sub_mem_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate


section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem opensι_appLE_self_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel ..
private theorem germ_topIso_inv_mem_maximalIdeal {X₁ : Scheme.{u}} (V : X₁.Opens) (y : ↥X₁)
    (hy : y ∈ V) (htop : pointOfMem V y hy ∈ (⊤ : (V.toScheme).Opens)) (s : Γ(X₁, V))
    (hs : (X₁.presheaf.germ V y hy).hom s ∈ IsLocalRing.maximalIdeal ↑(X₁.presheaf.stalk y)) :
    (V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop).hom (V.topIso.inv.hom s) ∈
      IsLocalRing.maximalIdeal ↑(V.toScheme.presheaf.stalk (pointOfMem V y hy)) := by
  have e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ => z.2
  have hy' : pointOfMem V y hy ∈ V.ι ⁻¹ᵁ V := hy
  have hnu : ¬ IsUnit ((X₁.presheaf.germ V y hy).hom s) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
    exact hs
  have happ : V.topIso.inv = V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE e).op :=
    (opensι_appLE_self_top_eq_topIso_inv V e).symm
  have h1 : V.topIso.inv ≫ V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop
      = V.ι.app V ≫ V.toScheme.presheaf.germ (V.ι ⁻¹ᵁ V) (pointOfMem V y hy) hy' := by
    rw [happ, Category.assoc, TopCat.Presheaf.germ_res]
  have h2 : (V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop).hom (V.topIso.inv.hom s)
      = (V.toScheme.presheaf.germ (V.ι ⁻¹ᵁ V) (pointOfMem V y hy) hy').hom
          ((V.ι.app V).hom s) := by
    have h := congrArg
      (fun f : Γ(X₁, V) ⟶ V.toScheme.presheaf.stalk (pointOfMem V y hy) =>
        CommRingCat.Hom.hom f s) h1
    exact h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, h2]
  intro hu
  apply hnu
  have hmem : pointOfMem V y hy ∈ V.ι ⁻¹ᵁ (X₁.basicOpen s) := by
    rw [Scheme.preimage_basicOpen]
    exact (V.toScheme.mem_basicOpen ((V.ι.app V).hom s) (pointOfMem V y hy) hy').2 hu
  exact (X₁.mem_basicOpen s y hy).1 hmem
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (x : X) (hx : x ∈ U)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x)) :
    ChartsAgreeAt c₁ c₂ x hx := by
  refine chartsAgreeAt_of_germ_sub_mem_maximalIdeal c₁ c₂ x hx ?_
  intro i
  by_cases hij : i = j
  · rw [hij]
    have e1 : U.topIso.inv.hom (c₁.coord j) = c₁.coordTop j :=
      Iso.hom_inv_id_apply U.topIso (c₁.coordTop j)
    have e2 : U.topIso.inv.hom (c₂.coord j) = c₂.coordTop j :=
      Iso.hom_inv_id_apply U.topIso (c₂.coordTop j)
    have h1 := germ_topIso_inv_mem_maximalIdeal U x hx (by trivial) (c₁.coord j) hg₁
    have h2 := germ_topIso_inv_mem_maximalIdeal U x hx (by trivial) (c₂.coord j) hg₂
    rw [e1] at h1
    rw [e2] at h2
    rw [map_sub]
    exact Submodule.sub_mem _ h1 h2
  · have hc := hcoord i hij
    have h' : U.topIso.inv.hom (U.topIso.hom.hom (c₁.coordTop i))
        = U.topIso.inv.hom (U.topIso.hom.hom (c₂.coordTop i)) :=
      congrArg (fun z => U.topIso.inv.hom z) hc
    have h'' : c₁.coordTop i = c₂.coordTop i :=
      (Iso.hom_inv_id_apply U.topIso (c₁.coordTop i)).symm.trans
        (h'.trans (Iso.hom_inv_id_apply U.topIso (c₂.coordTop i)))
    rw [h'', sub_self, map_zero]
    exact Submodule.zero_mem _
end FunctorialResolution.EmbeddedResolution
