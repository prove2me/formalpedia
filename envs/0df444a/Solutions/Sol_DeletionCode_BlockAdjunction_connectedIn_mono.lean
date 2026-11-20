-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.connectedIn_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:10.528943+00:00
-- url     : https://prove2.me/submissions/069c1827-f12a-42d7-90ab-d190d16089fc

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {k : ℕ} {U V : RuleSet k} (hUV : U ⊆ V)
    {a b : Gram (windowLength k) → ℤ} (h : ConnectedIn U a b) : ConnectedIn V a b := by
  induction h with
  | rel a b hab =>
    exact Relation.EqvGen.rel _ _ ⟨hUV hab.1, hUV hab.2.1, hab.2.2⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
end DeletionCode.BlockAdjunction
