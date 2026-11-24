-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_generalizingMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:32.418806+00:00
-- url     : https://prove2.me/submissions/17a0f69f-85d3-4bd8-87f8-f7230a60ec49

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IrreducibleComponentsFlatPreimage

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
theorem _root_.solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hcont : Continuous (fun x : ↥X => f x) := f.base.hom.continuous
  constructor
  · intro hx
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hη' : closure ({η} : Set ↥Y) = C := hη
    have hxmem : (fun x : ↥X => f x) x ∈ closure ({η} : Set ↥Y) := by
      rw [hη']
      exact hx
    have hspec : η ⤳ (fun x : ↥X => f x) x := specializes_iff_mem_closure.mpr hxmem
    obtain ⟨x', hx'spec, hfx'⟩ := hf hspec
    refine ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x',
      ?_, ?_⟩
    · have hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x' :=
        closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent)
          isClosed_irreducibleComponent
      exact hsub (specializes_iff_mem_closure.mp hx'spec)
    · have hsub : C ⊆ closure ((fun x : ↥X => f x) '' irreducibleComponent x') := by
        rw [← hη']
        refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure
        exact subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩
      have hirr : IsIrreducible (closure ((fun x : ↥X => f x) '' irreducibleComponent x')) :=
        (isIrreducible_irreducibleComponent.image (fun x : ↥X => f x)
          hcont.continuousOn).closure
      exact Set.Subset.antisymm (hC.2 hirr hsub) hsub
  · rintro ⟨C', -, hxC', rfl⟩
    exact subset_closure ⟨x, hxC', rfl⟩
end FunctorialResolution.EmbeddedResolution
