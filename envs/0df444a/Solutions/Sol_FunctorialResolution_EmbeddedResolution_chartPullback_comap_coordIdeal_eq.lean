-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartPullback_comap_coordIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:36.404412+00:00
-- url     : https://prove2.me/submissions/2771521f-9c6d-40b7-8a1c-7146e89ecf55

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (c₁ c₂ : EtaleChart q V n) (S : Finset (Fin n)) :
    (c₁.coordIdeal S).comap (pullback.fst c₁.map c₂.map) =
      (c₂.coordIdeal S).comap (pullback.snd c₁.map c₂.map) := by
  rw [c₁.coordIdeal_eq_comap_coordSubspaceIdeal S, c₂.coordIdeal_eq_comap_coordSubspaceIdeal S, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]
end FunctorialResolution.EmbeddedResolution
