-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:58.344053+00:00
-- url     : https://prove2.me/submissions/29569ef1-bbc0-4b87-8ea9-22700b7cffbf

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_def
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
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


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem appTop_hom_appTop_inv_apply {A B : Scheme.{u}} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (Scheme.Hom.appTop e.hom).hom ((Scheme.Hom.appTop e.inv).hom x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom = 𝟙 Γ(A, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  have h2 := congrArg (fun f : Γ(A, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom f x) h
  simpa using h2
private theorem affineSpace_specIso_inv_appTop_coord (K : Type u) [Field K] (n : ℕ) (j : Fin n) :
    ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)))
      = ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom
          (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n))) := by
  exact AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of K) (ULift.up j)
private theorem affineSpaceGlobalSectionsHom_X (K : Type u) [Field K] (n : ℕ) (j : Fin n) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X (ULift.up j : ULift.{u} (Fin n)))
      = AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin n)) := by
  simp only [affineSpaceGlobalSectionsHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← affineSpace_specIso_inv_appTop_coord K n j]
  exact appTop_hom_appTop_inv_apply _ _
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
theorem _root_.solution (c : EtaleChart p U m) (j : Fin m) :
    c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j := by
  rw [EtaleChart.coordRingHom_def, EtaleChart.coord_def]
  simp only [RingHom.comp_apply, affineSpaceGlobalSectionsHom_X]
end EtaleChart
end FunctorialResolution.EmbeddedResolution
