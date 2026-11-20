-- Prove2me | solution 1 for DeletionCode.SignedSupport.supported_iff_signed_incident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:25.6222+00:00
-- url     : https://prove2.me/submissions/ffb44ff4-806f-47b0-bd1d-148bb0569367

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_signed_support_edge_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (v : SupportComponents.Vertex L) :
    (∃ b, SupportComponents.HasVertex F L b v) ↔
      ∃ w, signedSupportEdge F L v w ∨ signedSupportEdge F L w v := by
  constructor
  · rintro ⟨b, side, i, hi, hv⟩
    by_cases hbefore : i ≤ F.extra b side
    · refine ⟨SupportComponents.vertex F L b side (i + 1), Or.inl ?_⟩
      apply (signed_support_edge_iff F L H hdis _ _).mpr
      exact ⟨b, side, i, hbefore, hv, rfl⟩
    · have hlast : i = F.extra b side + 1 := by omega
      refine ⟨SupportComponents.vertex F L b side (F.extra b side), Or.inr ?_⟩
      apply (signed_support_edge_iff F L H hdis _ _).mpr
      refine ⟨b, side, F.extra b side, le_rfl, rfl, ?_⟩
      simpa only [hlast] using hv
  · rintro ⟨w, h | h⟩
    · obtain ⟨b, hv, _⟩ := SupportComponents.edge_owners F L
        ((signed_support_edge_iff F L H hdis _ _).mp h)
      exact ⟨b, hv⟩
    · obtain ⟨b, _, hv⟩ := SupportComponents.edge_owners F L
        ((signed_support_edge_iff F L H hdis _ _).mp h)
      exact ⟨b, hv⟩
end DeletionCode.SignedSupport
