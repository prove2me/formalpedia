-- Prove2me | solution 1 for CGWH.onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:56:15.261798+00:00
-- url     : https://prove2.me/submissions/d320a28e-c322-49f1-a434-fd55fc5cd578

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite

/-- If every compact subset of the `T1` space `Y` is finite and `OnePoint Y` is compactly
generated, then `Y` is discrete. -/
theorem not_cg (Y : Type u) [TopologicalSpace Y] [T1Space Y]
    (hfin : ∀ K : Set Y, IsCompact K → K.Finite) (hnd : ¬ DiscreteTopology Y) :
    ¬ CompactlyGeneratedSpace (OnePoint Y) := by
  intro hCG
  apply hnd
  rw [discreteTopology_iff_forall_isOpen]
  intro U
  rw [← OnePoint.isOpen_image_coe]
  refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ g hg => ?_
  rw [isOpen_iff_mem_nhds]
  intro k hk
  have hV : IsOpen (g ⁻¹' Set.range ((↑) : Y → OnePoint Y)) :=
    OnePoint.isOpen_range_coe.preimage hg
  have hkV : k ∈ g ⁻¹' Set.range ((↑) : Y → OnePoint Y) := by
    obtain ⟨y, -, hy⟩ := hk; exact ⟨y, hy⟩
  obtain ⟨L, hLnhds, hLsub, hLcomp⟩ := local_compact_nhds (hV.mem_nhds hkV)
  have hgL : IsCompact (g '' L) := hLcomp.image hg
  have hS : IsCompact (((↑) : Y → OnePoint Y) ⁻¹' (g '' L)) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff,
      Set.image_preimage_eq_of_subset]
    · exact hgL
    · rintro _ ⟨l, hl, rfl⟩; exact hLsub hl
  have hSfin := hfin _ hS
  let W : Set K :=
    (⋃ y ∈ (((↑) : Y → OnePoint Y) ⁻¹' (g '' L)) \ U, g ⁻¹' {(y : OnePoint Y)})ᶜ
  have hWopen : IsOpen W := by
    exact ((hSfin.subset Set.sdiff_subset).isClosed_biUnion
      fun y _ => isClosed_singleton.preimage hg).isOpen_compl
  have hkW : k ∈ W := by
    simp only [W, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    rintro y ⟨-, hyU⟩ hgy
    obtain ⟨y', hy'U, hy'⟩ := hk
    have hgy' : g k = (y : OnePoint Y) := hgy
    rw [hgy'] at hy'
    exact hyU (OnePoint.coe_injective hy' ▸ hy'U)
  refine Filter.mem_of_superset (Filter.inter_mem hLnhds (hWopen.mem_nhds hkW)) ?_
  rintro l ⟨hlL, hlW⟩
  obtain ⟨y, hy⟩ := hLsub hlL
  by_contra hl
  apply hlW
  simp only [Set.mem_iUnion]
  exact ⟨y, ⟨⟨l, hlL, hy.symm⟩, fun hyU => hl ⟨y, hyU, hy⟩⟩, hy.symm⟩

/-- If every compact subset of the `T1` space `Y` is finite and `Y` is compactly coherent,
then `Y` is discrete. -/
theorem not_cc (Y : Type u) [TopologicalSpace Y] [T1Space Y]
    (hfin : ∀ K : Set Y, IsCompact K → K.Finite) (hnd : ¬ DiscreteTopology Y) :
    ¬ CompactlyCoherentSpace Y := by
  intro h
  apply hnd
  rw [discreteTopology_iff_forall_isOpen]
  intro U
  rw [CompactlyCoherentSpace.isOpen_iff]
  intro K hK
  have : Finite K := (hfin K hK).to_subtype
  exact isOpen_discrete _

end Sol_CGWH_onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite



theorem solution
    (Y : Type u) [TopologicalSpace Y] [T1Space Y]
    (hfin : ∀ K : Set Y, IsCompact K → K.Finite) (hnd : ¬ DiscreteTopology Y) :
    ¬ CompactlyGeneratedSpace (OnePoint Y) ∧ ¬ CompactlyCoherentSpace Y :=
  ⟨Sol_CGWH_onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite.not_cg Y hfin hnd,
    Sol_CGWH_onePoint_not_compactlyGeneratedSpace_of_forall_isCompact_finite.not_cc Y hfin hnd⟩
