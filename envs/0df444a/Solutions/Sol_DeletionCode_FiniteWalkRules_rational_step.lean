-- Prove2me | solution 1 for DeletionCode.FiniteWalkRules.rational_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:29:10.503216+00:00
-- url     : https://prove2.me/submissions/38a459cd-6b56-4685-bf76-07d023acd2a7

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}
namespace DeletionCode.FiniteWalkRules
theorem _root_.solution
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (i : Fin m) :
    rational (step p i) = walkStep (rationalPath p) i := by
  funext g
  simp [rational, step, walkStep, rationalPath]
end DeletionCode.FiniteWalkRules
