-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_lastStructMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:58:48.59663+00:00
-- url     : https://prove2.me/submissions/56cf18b9-1c8b-4132-84f5-111b30ae68f2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_objNontrivialIndexZeroIso_hom
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
variable {X : Scheme.{u}}
private theorem projectionToBase_eq_eqToHom_comp (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    s.projectionToBase a = eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b := by
  subst h
  simp
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
theorem _root_.solution (s : SequenceOfBlowups X) :
    s.withoutIsoBlowups.lastStructMap = eqToHom s.withoutIsoBlowups_lastObj ≫ s.lastStructMap := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  have h1 : s.withoutIsoBlowups.lastStructMap = s.projectionToBase (s.nontrivialIndex s.withoutIsoBlowups.length) := by
    rw [lastStructMap_eq_projectionToBase, projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase _
  rw [h1, lastStructMap_eq_projectionToBase]
  exact projectionToBase_eq_eqToHom_comp s s.nontrivialIndex_lengthWithoutIsoBlowups
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
