-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.support_path_in_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:24.082772+00:00
-- url     : https://prove2.me/submissions/b5c90a54-5ac8-48ae-bf85-807307247117

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_edge_in_block
import Theorems.Thm_DeletionCode_SupportBlockCount_support_path_incident_iff
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (hpath : RuleSetConnected G u v) :
    Incident B u → RuleSetConnected B u v := by
  induction hpath with
  | rel u v he =>
    intro hu
    exact Relation.EqvGen.rel _ _ (edge_in_block G B hB he hu)
  | refl u =>
    intro hu
    exact Relation.EqvGen.refl _
  | symm u v h ih =>
    intro hv
    have hu := (support_path_incident_iff G B hB h).mpr hv
    exact Relation.EqvGen.symm _ _ (ih hu)
  | trans u v z huv hvz ihu ihv =>
    intro hu
    have hv := (support_path_incident_iff G B hB huv).mp hu
    exact Relation.EqvGen.trans _ _ _ (ihu hu) (ihv hv)
end DeletionCode.SupportBlockCount
