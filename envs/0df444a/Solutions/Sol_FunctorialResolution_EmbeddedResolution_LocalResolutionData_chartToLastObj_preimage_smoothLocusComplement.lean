-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.chartToLastObj_preimage_smoothLocusComplement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:30:02.642875+00:00
-- url     : https://prove2.me/submissions/fce459a0-caa9-44a9-9415-1d42c3c30a0b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionStrictNormalCrossings
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_chartToLastObj_comp_lastStructMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_preimage_smoothLocusComplement_cover_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have hcomp := d.chartToLastObj_comp_lastStructMap i
  have hsl := d.preimage_smoothLocusComplement_cover_map i
  ext x
  simp only [Set.mem_preimage]
  have hx : s.lastStructMap.base ((d.chartToLastObj i).base x)
      = (d.cover.f i).base ((d.seq i).lastStructMap.base x) := by
    have h := congrArg (fun g : (d.seq i).lastObj ⟶ X => g.base x) hcomp
    simpa using h
  rw [hx, ← Set.mem_preimage, hsl]
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
