-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.chartToLastObj_comp_lastStructMap_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:30:01.543805+00:00
-- url     : https://prove2.me/submissions/bbdf739c-12d6-450a-9a7c-ebc50320d7a4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionSmooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← Category.assoc, d.chartToLastObj_comp_lastStructMap j, Category.assoc]
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
