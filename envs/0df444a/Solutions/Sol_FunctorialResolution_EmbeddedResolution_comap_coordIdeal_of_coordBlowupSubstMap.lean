-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_coordIdeal_of_coordBlowupSubstMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.01469+00:00
-- url     : https://prove2.me/submissions/64f31318-71ee-4830-8024-5c8ade0f0ab3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map) (T : Finset (Fin m)) :
    (c.coordIdeal T).comap g =
      ((coordSubspaceIdeal k m T).comap (coordBlowupSubstMap k m S s)).comap c₁.map := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp, ← hg,
    Scheme.IdealSheafData.comap_comp]
end FunctorialResolution.EmbeddedResolution
