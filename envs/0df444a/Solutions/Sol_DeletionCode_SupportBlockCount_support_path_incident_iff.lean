-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.support_path_incident_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:53.012785+00:00
-- url     : https://prove2.me/submissions/db58576e-eea6-482c-83be-11e0464979e1

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_edge_incident_iff
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u ↔ Incident B v := by
  induction hpath with
  | rel u v he => exact edge_incident_iff G B hB he
  | refl u => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v z huv hvz ihu ihv => exact ihu.trans ihv
end DeletionCode.SupportBlockCount
