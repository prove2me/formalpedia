-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.blockOf_insert_eq_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:58.595476+00:00
-- url     : https://prove2.me/submissions/1e377c33-145a-442c-a93d-a9f54cc28d11

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
import Theorems.Thm_DeletionCode_LargeBlockSelection_blockOf_insert_subset_of_not_mem
import Theorems.Thm_DeletionCode_BlockAdjunction_connectedIn_mono
import Theorems.Thm_DeletionCode_BlockAdjunction_path_within_block
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf



set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction
namespace DeletionCode.LargeBlockSelection
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) :
    blockOf (insert w G) a = blockOf G a := by
  classical
  have hsub := blockOf_insert_subset_of_not_mem G w a hw
  ext b
  constructor
  · intro hb
    have hab := ((mem_blockOf (insert w G) a b).mp hb).2
    have hpath : ConnectedIn (blockOf (insert w G) a) a b :=
      path_within_block (insert w G) hab a (Relation.EqvGen.refl a)
    exact (mem_blockOf G a b).mpr
      ⟨hsub hb, connectedIn_mono hsub hpath⟩
  · intro hb
    obtain ⟨hbG, hab⟩ := (mem_blockOf G a b).mp hb
    exact (mem_blockOf (insert w G) a b).mpr
      ⟨Finset.mem_insert_of_mem hbG,
        connectedIn_mono (Finset.subset_insert w G) hab⟩
end DeletionCode.LargeBlockSelection
