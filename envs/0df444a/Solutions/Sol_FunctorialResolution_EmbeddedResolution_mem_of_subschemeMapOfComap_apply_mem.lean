-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_of_subschemeMapOfComap_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:10.501789+00:00
-- url     : https://prove2.me/submissions/adb60bf9-cf21-4815-8b35-f6892a2d582c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_subschemeMapOfComap_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (A : Set X) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (y : (Z.comap g).subscheme) (hy : (subschemeMapOfComap g Z).base y ∈ W) : y ∈ W' := by
  have hcont : Continuous ⇑(subschemeMapOfComap g Z).base :=
    (subschemeMapOfComap g Z).base.hom.continuous
  have hyW : connectedComponent ((subschemeMapOfComap g Z).base y) ⊆ ⇑Z.subschemeι.base ⁻¹' A := by
    have h0 : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := hy
    rw [hW] at h0
    exact h0
  have himg : ⇑(subschemeMapOfComap g Z).base '' connectedComponent y ⊆
      connectedComponent ((subschemeMapOfComap g Z).base y) :=
    IsPreconnected.subset_connectedComponent
      (isPreconnected_connectedComponent.image _ hcont.continuousOn)
      ⟨y, mem_connectedComponent, rfl⟩
  have hmem : y ∈ (W' : Set (Z.comap g).subscheme) := by
    rw [hW']
    intro z hz
    have h1 : (subschemeMapOfComap g Z).base z ∈
        connectedComponent ((subschemeMapOfComap g Z).base y) := himg ⟨z, hz, rfl⟩
    have h2 : Z.subschemeι.base ((subschemeMapOfComap g Z).base z) ∈ A := hyW h1
    rw [subschemeMapOfComap_base g Z z] at h2
    exact h2
  exact hmem
end FunctorialResolution.EmbeddedResolution
