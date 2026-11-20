-- Prove2me | solution 1 for DeletionCode.BlockPartition.incident_iff_rule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:15.965597+00:00
-- url     : https://prove2.me/submissions/a5ee36f2-b209-45f7-80ab-4dd440adfd65

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (v : SupportComponents.Vertex (windowLength k)) :
    Incident U v ↔ ∃ w ∈ U, Incident {w} v := by
  classical
  constructor
  · rintro ⟨u, ⟨w, hw, g, hg, hv, hu⟩ | ⟨w, hw, g, hg, hu, hv⟩⟩
    · exact ⟨w, hw, u, Or.inl ⟨w, Finset.mem_singleton_self w, g, hg, hv, hu⟩⟩
    · exact ⟨w, hw, u, Or.inr ⟨w, Finset.mem_singleton_self w, g, hg, hu, hv⟩⟩
  · rintro ⟨w, hw, hv⟩
    exact ComponentBounds.incident_mono (Finset.singleton_subset_iff.mpr hw) hv
end DeletionCode.BlockPartition
