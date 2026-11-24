-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:53.140017+00:00
-- url     : https://prove2.me/submissions/b906f46a-97fd-4a08-9bfe-ca62e7d57a73

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U V : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (hVU : V ≤ U) (j : Fin m) :
    (c.restrict hVU).coord j = (X.presheaf.map (homOfLE hVU).op).hom (c.coord j) := by
  have key : ∀ {A B C D : (Opens ↥X)ᵒᵖ} {R : CommRingCat.{u}} (f : R ⟶ X.presheaf.obj A)
      (α : A ⟶ B) (β : B ⟶ D) (γ : A ⟶ C) (δ : C ⟶ D) (z : R),
      (X.presheaf.map β).hom ((f ≫ X.presheaf.map α).hom z)
        = (X.presheaf.map δ).hom ((X.presheaf.map γ).hom (f.hom z)) := by
    intro A B C D R f α β γ δ z
    have h : X.presheaf.map α ≫ X.presheaf.map β = X.presheaf.map γ ≫ X.presheaf.map δ :=
      (X.presheaf.map_comp α β).symm.trans
        ((congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans
          (X.presheaf.map_comp γ δ))
    exact congrArg (fun g : X.presheaf.obj A ⟶ X.presheaf.obj D => g.hom (f.hom z)) h
  simp [EtaleChart.restrict, EtaleChart.coord]
  all_goals
    first
      | rfl
      | exact key _ _ _ _ _ _
end EtaleChart
end FunctorialResolution.EmbeddedResolution
