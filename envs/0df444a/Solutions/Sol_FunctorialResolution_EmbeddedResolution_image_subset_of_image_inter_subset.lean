-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.image_subset_of_image_inter_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:05.176417+00:00
-- url     : https://prove2.me/submissions/af4063d0-fd43-4f3b-aa9f-f92d7e815b3a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {A O : Set α} {g : α → β} {C : Set β} (hA : IsIrreducible A)
    (hO : IsOpen O) (hAO : (A ∩ O).Nonempty) (hg : Continuous g) (hC : IsClosed C)
    (h : g '' (A ∩ O) ⊆ C) : g '' A ⊆ C := by
  have hsub : A ⊆ closure (A ∩ O) := by
    intro x hx
    rw [mem_closure_iff]
    intro u hu hxu
    obtain ⟨z, hz⟩ := hA.2 u O hu hO ⟨x, hx, hxu⟩ hAO
    exact ⟨z, hz.2.1, hz.1, hz.2.2⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : g x ∈ g '' closure (A ∩ O) := ⟨x, hsub hx, rfl⟩
  exact closure_minimal h hC (image_closure_subset_closure_image hg h1)
end FunctorialResolution.EmbeddedResolution
