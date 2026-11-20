-- Prove2me | solution 1 for DeletionCode.BlockPartition.blocks_support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:41.405508+00:00
-- url     : https://prove2.me/submissions/5d97d9fd-0b71-407f-9b11-70a8a10232f3

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_BlockPartition_blockOf_eq_of_connected
import Theorems.Thm_DeletionCode_BlockPartition_incident_iff_rule
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k) :
    ∀ B ∈ blocks U, ∀ C ∈ blocks U, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v := by
  intro B hB C hC hne v hvB hvC
  obtain ⟨a, ha, rfl⟩ := (mem_blocks U B).mp hB
  obtain ⟨d, hd, rfl⟩ := (mem_blocks U C).mp hC
  obtain ⟨b, hb, hvb⟩ := (incident_iff_rule (blockOf U a) v).mp hvB
  obtain ⟨c, hc, hvc⟩ := (incident_iff_rule (blockOf U d) v).mp hvC
  obtain ⟨hbU, hab⟩ := (mem_blockOf U a b).mp hb
  obtain ⟨hcU, hdc⟩ := (mem_blockOf U d c).mp hc
  have hbc : ConnectedIn U b c :=
    Relation.EqvGen.rel _ _ ⟨hbU, hcU, v, hvb, hvc⟩
  have had : ConnectedIn U a d := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.trans _ _ _ hab hbc) (Relation.EqvGen.symm _ _ hdc)
  exact hne (blockOf_eq_of_connected U a d had)
end DeletionCode.BlockPartition
