-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.preimage_smoothLocusComplement_cover_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:24:59.593539+00:00
-- url     : https://prove2.me/submissions/7a373609-4d0c-43be-b154-f0ca5ea83ecd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
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
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.cover.f i).base ⁻¹' ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((smoothLocusComplement (d.cover.f i ≫ f) :
          TopologicalSpace.Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have h : ((d.cover.f i).base ⁻¹' (f.smoothLocus : Set ↥X))
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i)) :=
    congrArg (fun U : TopologicalSpace.Opens ↥(d.cover.X i) => (U : Set ↥(d.cover.X i)))
      (d.preimage_smoothLocus_cover_map i)
  show (d.cover.f i).base ⁻¹' ((f.smoothLocus : Set ↥X))ᶜ
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i))ᶜ
  rw [Set.preimage_compl, h]
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
