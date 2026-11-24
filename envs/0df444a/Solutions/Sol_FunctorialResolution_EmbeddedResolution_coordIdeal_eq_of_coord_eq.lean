-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.coordIdeal_eq_of_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:38:33.017961+00:00
-- url     : https://prove2.me/submissions/e89435a0-fe9e-43bd-9c62-07ae561ea346

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
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {n : ℕ} (hU : IsAffineOpen U) (c₁ c₂ : EtaleChart p U n)
    (S : Finset (Fin n)) (h : ∀ i ∈ S, c₁.coord i = c₂.coord i) :
    c₁.coordIdeal S = c₂.coordIdeal S := by
  have hUaff : IsAffine U.toScheme := hU
  have hcf : ∀ i ∈ S,
      (c₁.map.appTop).hom (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up i : ULift.{u} (Fin n)))
        = (c₂.map.appTop).hom (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up i : ULift.{u} (Fin n))) := by
    intro i hi
    have h1 := congrArg (fun z : Γ(X, U) => U.topIso.inv.hom z) (h i hi)
    have key : c₁.coordTop i = c₂.coordTop i :=
      (Iso.hom_inv_id_apply U.topIso (c₁.coordTop i)).symm.trans
        (h1.trans (Iso.hom_inv_id_apply U.topIso (c₂.coordTop i)))
    exact key
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Scheme.IdealSheafData.comap_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_span, Ideal.map_span]
  refine congrArg Scheme.IdealSheafData.ofIdealTop (congrArg Ideal.span ?_)
  refine Set.image_congr ?_
  rintro _ ⟨i, hi, rfl⟩
  exact hcf i (Finset.mem_coe.mp hi)
end FunctorialResolution.EmbeddedResolution
