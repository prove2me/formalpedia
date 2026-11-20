-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.blockOf_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:32.707459+00:00
-- url     : https://prove2.me/submissions/6cbe1c73-01f9-4c33-9c80-1e82c974d3ca

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf



set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
theorem _root_.solution {k : ℕ} (G : RuleSet k) (a : Gram (windowLength k) → ℤ) :
    ClosedIn G (blockOf G a) := by
  intro b hb c hc hbc
  exact (mem_blockOf G a c).mpr
    ⟨hc, Relation.EqvGen.trans _ _ _ ((mem_blockOf G a b).mp hb).2 hbc⟩
end DeletionCode.FiniteGenerating
