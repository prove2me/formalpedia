-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.blockHull_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:55.876095+00:00
-- url     : https://prove2.me/submissions/f8f8f305-4b26-498e-b413-32b23e61959e

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

section
namespace DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
private theorem induced_mem_iff {k : ℕ} (G : RuleSet k)
    {a b : Gram (windowLength k) → ℤ}
    (h : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    a ∈ G ↔ b ∈ G := by
  induction h with
  | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
  | refl a => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
end DeletionCode.RelationBlockSavings
end

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {k : ℕ} (G I : RuleSet k)
    {a b : Gram (windowLength k) → ℤ} (ha : a ∈ blockHull G I)
    (hpath : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    b ∈ blockHull G I := by
  classical
  obtain ⟨haG, i, hi, hia⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨(induced_mem_iff G hpath).mp haG,
    i, hi, Relation.EqvGen.trans i a b hia hpath⟩
end DeletionCode.RelationBlockSavings
