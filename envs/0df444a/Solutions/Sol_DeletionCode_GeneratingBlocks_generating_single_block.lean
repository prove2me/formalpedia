-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.generating_single_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:25.379186+00:00
-- url     : https://prove2.me/submissions/12e19ecd-e19e-403e-9522-f0465894c049

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_restrict

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (a : I)
    (hgen : Generating v G rank) :
    Generating v (fun i : {i // Connected G a i} => G i.val)
      (fun i : {i // Connected G a i} => rank i.val) := by
  apply generating_restrict v G rank {i | Connected G a i} hgen
  intro i hi j hij
  exact Relation.EqvGen.trans a i j hi hij
end DeletionCode.GeneratingBlocks
