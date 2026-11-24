-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartPullbackFstStalkMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:00.980276+00:00
-- url     : https://prove2.me/submissions/0eeb9539-e7e9-4f89-b579-9c448a98bbfc

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct

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
theorem _root_.solution (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackFstStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := rfl
end FunctorialResolution.EmbeddedResolution
