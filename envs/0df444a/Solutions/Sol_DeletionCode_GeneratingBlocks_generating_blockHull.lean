-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.generating_blockHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:21.656176+00:00
-- url     : https://prove2.me/submissions/54025f83-24ad-49a3-a6c5-9b6c0a2edb24

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_restrict
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (T : Set I)
    (hgen : Generating v G rank) :
    Generating v (fun i : blockHull G T => G i.val)
      (fun i : blockHull G T => rank i.val) :=
  generating_restrict v G rank (blockHull G T) hgen (blockHull_closed G T)
end DeletionCode.GeneratingBlocks
