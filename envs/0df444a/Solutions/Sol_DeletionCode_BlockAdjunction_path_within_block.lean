-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.path_within_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:14.489666+00:00
-- url     : https://prove2.me/submissions/f534a2d9-d179-4cad-9918-5ac4cc73682d

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf



set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    {b c : Gram (windowLength k) → ℤ} (hbc : ConnectedIn U b c) :
    ∀ a, ConnectedIn U a b → ConnectedIn (blockOf U a) b c := by
  induction hbc with
  | rel b c hbc =>
    intro a hab
    have hb : b ∈ blockOf U a := (mem_blockOf U a b).mpr ⟨hbc.1, hab⟩
    have hc : c ∈ blockOf U a := (mem_blockOf U a c).mpr
      ⟨hbc.2.1, Relation.EqvGen.trans _ _ _ hab (Relation.EqvGen.rel _ _ hbc)⟩
    exact Relation.EqvGen.rel _ _ ⟨hb, hc, hbc.2.2⟩
  | refl b =>
    intro a hab
    exact Relation.EqvGen.refl _
  | symm b c hbc ih =>
    intro a hac
    have hab : ConnectedIn U a b :=
      Relation.EqvGen.trans _ _ _ hac (Relation.EqvGen.symm _ _ hbc)
    exact Relation.EqvGen.symm _ _ (ih a hab)
  | trans b c d hbc hcd ihbc ihcd =>
    intro a hab
    exact Relation.EqvGen.trans _ _ _ (ihbc a hab)
      (ihcd a (Relation.EqvGen.trans _ _ _ hab hbc))
end DeletionCode.BlockAdjunction
