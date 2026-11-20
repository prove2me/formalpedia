-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.block_count_le_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:23.36557+00:00
-- url     : https://prove2.me/submissions/dbdb8d81-b42e-4d87-acec-f212d1f15ed3

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_support_path_incident_iff
import Theorems.Thm_DeletionCode_BlockPartition_blocks_support_disjoint
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ componentCount {w} := by
  classical
  let select : Bs → RuleSetVertex {w} := fun B =>
    ⟨Classical.choose (hhit B.val B.property),
      (Classical.choose_spec (hhit B.val B.property)).2⟩
  have hselect (B : Bs) : Incident B.val (select B).val :=
    (Classical.choose_spec (hhit B.val B.property)).1
  let encode : Bs → RuleSetComponents {w} := fun B =>
    Quotient.mk (ruleSetSetoid {w}) (select B)
  have hinj : Function.Injective encode := by
    intro B C heq
    apply Subtype.ext
    by_contra hne
    have hpathW : RuleSetConnected {w} (select B).val (select C).val :=
      Quotient.exact heq
    have hpathG : RuleSetConnected G (select B).val (select C).val :=
      SupportInclusion.connected_mono hsub hpathW
    have hCvertexB : Incident B.val (select C).val :=
      (support_path_incident_iff G B.val (hBs B.property) hpathG).mp (hselect B)
    exact blocks_support_disjoint G B.val (hBs B.property) C.val (hBs C.property)
      hne (select C).val hCvertexB (hselect C)
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [componentCount, Nat.card_eq_fintype_card] using hcard
end DeletionCode.SupportBlockCount
