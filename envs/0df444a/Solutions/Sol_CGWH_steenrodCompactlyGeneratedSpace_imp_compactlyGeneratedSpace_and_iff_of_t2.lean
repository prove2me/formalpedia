-- Prove2me | solution 1 for CGWH.steenrodCompactlyGeneratedSpace_imp_compactlyGeneratedSpace_and_iff_of_t2
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:53:29.985079+00:00
-- url     : https://prove2.me/submissions/9868b4a5-bd55-458f-97f4-634b023cf9ce

import Definitions.Def_CGWH_SteenrodCompactlyGenerated

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

theorem solution
    (X : Type u) [TopologicalSpace X] :
    (SteenrodCompactlyGeneratedSpace X → CompactlyGeneratedSpace X) ∧
      (T2Space X → (CompactlyGeneratedSpace X ↔ SteenrodCompactlyGeneratedSpace X)) := by
  have h1 : SteenrodCompactlyGeneratedSpace X → CompactlyGeneratedSpace X := by
    intro h
    refine compactlyGeneratedSpace_of_isOpen fun s hs => ?_
    refine h.isOpen_of_forall_isOpen_preimage_val s fun K hK _ => ?_
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact hs K Subtype.val continuous_subtype_val
  refine ⟨h1, fun hT2 => ⟨fun hCG => ?_, h1⟩⟩
  refine ⟨fun U hU => ?_⟩
  refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ f hf => ?_
  have h2 := (hU (Set.range f) (isCompact_range hf) inferInstance).preimage
    (hf.codRestrict Set.mem_range_self)
  rwa [← Set.preimage_comp] at h2
