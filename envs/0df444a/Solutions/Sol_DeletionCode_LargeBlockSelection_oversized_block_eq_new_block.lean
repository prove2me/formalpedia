-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.oversized_block_eq_new_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:52.143397+00:00
-- url     : https://prove2.me/submissions/5756c1e7-f934-4885-9266-aedc3ef9ea30

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
import Theorems.Thm_DeletionCode_LargeBlockSelection_block_not_containing_new_is_old
import Theorems.Thm_DeletionCode_LargeBlockSelection_block_containing_new_eq

set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction
namespace DeletionCode.LargeBlockSelection
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (B : RuleSet k) (hB : B ∈ blocks (insert w G)) (hlarge : L < B.card) :
    B = blockOf (insert w G) w := by
  classical
  by_cases hw : w ∈ B
  · exact block_containing_new_eq G w B hB hw
  · have hold := hsize B (block_not_containing_new_is_old G w B hB hw)
    omega
end DeletionCode.LargeBlockSelection
