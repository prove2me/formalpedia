-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartPullbackFst_comp_eq_chartPullbackSnd_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:39.909671+00:00
-- url     : https://prove2.me/submissions/b2ff0525-557a-40cc-bf4e-6cf58fbf8d16

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
theorem _root_.solution (c₁ c₂ : EtaleChart q V n) :
    chartPullbackFst c₁ c₂ ≫ q = chartPullbackSnd c₁ c₂ ≫ q := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map) ≫ affineSpaceFinToSpec k n
      = (pullback.snd c₁.map c₂.map ≫ c₂.map) ≫ affineSpaceFinToSpec k n := by
    rw [pullback.condition]
  rw [Category.assoc, Category.assoc] at h
  rw [c₁.comp_struct, c₂.comp_struct] at h
  simpa only [Category.assoc] using h
end FunctorialResolution.EmbeddedResolution
