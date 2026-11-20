-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.generating_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:05.707696+00:00
-- url     : https://prove2.me/submissions/99899908-97ee-4b4c-9830-cd79af3865e9

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
import Theorems.Thm_DeletionCode_GeneratingBlocks_supplier_connected

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (S : Set I)
    (hgen : Generating v G rank) (hclosed : BlockClosed G S) :
    Generating v (fun i : S => G i.val) (fun i : S => rank i.val) := by
  intro i g hneg
  rcases hgen i.val g hneg with hsource | ⟨j, hlt, hj⟩
  · exact Or.inl hsource
  · exact Or.inr ⟨⟨j, hclosed i.val i.property j
      (supplier_connected G i.val j g hneg hj)⟩, hlt, hj⟩
end DeletionCode.GeneratingBlocks
