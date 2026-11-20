-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.catalogue_block_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:29:22.044103+00:00
-- url     : https://prove2.me/submissions/b5ee40c0-242a-4668-87bf-fae4f1701f9a

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_block_count_le_components
import Theorems.Thm_DeletionCode_ConnectedBlocks_catalogue_singleton_component_count_le


set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (Bs : Finset (RuleSet k))
    (hw : CatalogueRule t k w) (hBs : Bs ⊆ blocks G)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G)
    (hhit : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v) :
    Bs.card ≤ 2 * t :=
  (block_count_le_components G w Bs hBs hsub hhit).trans
    (catalogue_singleton_component_count_le w hw)
end DeletionCode.SupportBlockCount
