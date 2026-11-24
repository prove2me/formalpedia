-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.subschemeMapOfComap_apply_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:54.422349+00:00
-- url     : https://prove2.me/submissions/d37918a5-fced-41e6-b214-59046be1dad5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_subschemeMapOfComap_base
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_generalizing_subschemeMapOfComap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_connectedComponent_of_specializes

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
theorem _root_.solution {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData)
    (A : Set X) (hA : IsClosed A) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w))
    (y : (Z.comap g).subscheme) (hy : y ∈ W') : (subschemeMapOfComap g Z).base y ∈ W := by
  have hyset : connectedComponent y ⊆
      ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := by
    have h0 : y ∈ (W' : Set (Z.comap g).subscheme) := hy
    rw [hW'] at h0
    exact h0
  have hcont : Continuous ⇑Z.subschemeι.base := Z.subschemeι.base.hom.continuous
  have hmem : (subschemeMapOfComap g Z).base y ∈ (W : Set Z.subscheme) := by
    rw [hW]
    have hC : IsIrreducible (connectedComponent ((subschemeMapOfComap g Z).base y)) :=
      hirr ((subschemeMapOfComap g Z).base y)
    obtain ⟨η, hηmem, hηspec⟩ :
        ∃ η, η ∈ connectedComponent ((subschemeMapOfComap g Z).base y) ∧
          ∀ z ∈ connectedComponent ((subschemeMapOfComap g Z).base y), η ⤳ z :=
      ⟨hC.genericPoint, (hC.isGenericPoint_genericPoint isClosed_connectedComponent).mem,
        fun z hz => (hC.isGenericPoint_genericPoint isClosed_connectedComponent).specializes hz⟩
    have hspec1 : η ⤳ (subschemeMapOfComap g Z).base y := hηspec _ mem_connectedComponent
    obtain ⟨y', hy'spec, hy'eq⟩ := generalizing_subschemeMapOfComap g Z y η hspec1
    have hy'cc : y' ∈ connectedComponent y := by
      have h1 : y ∈ connectedComponent y' :=
        mem_connectedComponent_of_specializes mem_connectedComponent hy'spec
      rw [← connectedComponent_eq h1]
      exact mem_connectedComponent
    have h3 : y' ∈ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A) := hyset hy'cc
    have h3' : g.base ((Z.comap g).subschemeι.base y') ∈ A := h3
    have h4 : Z.subschemeι.base η ∈ A := by
      rw [← hy'eq, subschemeMapOfComap_base g Z y']
      exact h3'
    intro x hx
    have hx2 : η ⤳ x := hηspec x hx
    have hx3 : Z.subschemeι.base η ⤳ Z.subschemeι.base x := hx2.map hcont
    exact hx3.mem_closed hA h4
  exact hmem
end FunctorialResolution.EmbeddedResolution
