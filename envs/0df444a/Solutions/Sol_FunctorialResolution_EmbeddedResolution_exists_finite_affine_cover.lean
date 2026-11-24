-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_finite_affine_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:27.715007+00:00
-- url     : https://prove2.me/submissions/e1f81f4d-19bb-4250-b698-0b6aafe7c945

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
universe u
private theorem exists_isAffineOpen_mem (Y : Scheme.{u}) (x : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U := by
  refine ⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange,
    isAffineOpen_opensRange _, ?_⟩
  exact Y.affineOpenCover.5 x
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  classical
  choose V hV hxV using exists_isAffineOpen_mem Y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (V x : Set Y))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
end FunctorialResolution.EmbeddedResolution
