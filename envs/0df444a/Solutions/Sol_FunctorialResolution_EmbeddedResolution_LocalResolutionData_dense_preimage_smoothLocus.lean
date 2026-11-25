-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.dense_preimage_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:03.374225+00:00
-- url     : https://prove2.me/submissions/d2c39dcd-3d48-42ed-98d1-3f60ebae5c3e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionDense
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_preimage_smoothLocus_cover_map


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
theorem _root_.solution (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
