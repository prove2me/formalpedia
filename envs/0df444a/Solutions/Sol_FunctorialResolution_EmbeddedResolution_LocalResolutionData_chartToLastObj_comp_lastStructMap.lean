-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.chartToLastObj_comp_lastStructMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:40.105963+00:00
-- url     : https://prove2.me/submissions/23d0443c-6131-43ee-a22c-7d0165b6e8cb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_lastObjIsoPullback_hom_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i ≫ s.lastStructMap = (d.seq i).lastStructMap ≫ d.cover.f i := by
  rw [d.chartToLastObj_eq i, Category.assoc, ← pullback.condition, ← Category.assoc,
    d.lastObjIsoPullback_hom_fst i]
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
