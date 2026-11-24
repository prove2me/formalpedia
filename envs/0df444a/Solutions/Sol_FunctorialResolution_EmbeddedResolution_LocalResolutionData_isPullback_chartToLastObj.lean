-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.isPullback_chartToLastObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:30:03.548065+00:00
-- url     : https://prove2.me/submissions/e5ff1a0d-c5ef-48c8-a746-8e8795a7990f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SmoothLocusIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap
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
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by
  have hsq : CommSq ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    ⟨(d.chartToLastObj_comp_lastStructMap i).symm⟩
  have h : IsPullback ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    IsPullback.of_iso_pullback hsq (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i)
      (d.chartToLastObj_eq i).symm
  exact h.flip
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
