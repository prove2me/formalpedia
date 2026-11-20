-- Prove2me | solution 1 for DeletionCode.AttachedBlocks.attached_union_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:17.041705+00:00
-- url     : https://prove2.me/submissions/fc124f0c-2e05-42fa-9f75-0188021dd804

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks
import Theorems.Thm_DeletionCode_AttachedBlocks_attached_block_count_le_vertices

set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators
namespace DeletionCode.AttachedBlocks
theorem _root_.solution {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    (insert w (Bs.biUnion id)).card ≤ 1 + L * Fintype.card (RuleSetVertex {w}) := by
  classical
  have hbi : (Bs.biUnion id).card ≤ ∑ B ∈ Bs, B.card := Finset.card_biUnion_le
  have hsum : (∑ B ∈ Bs, B.card) ≤ Bs.card * L := by
    calc
      (∑ B ∈ Bs, B.card) ≤ ∑ _ ∈ Bs, L := Finset.sum_le_sum hsize
      _ = Bs.card * L := by simp
  have hblocks := attached_block_count_le_vertices Bs w hmeet hdisjoint
  calc
    (insert w (Bs.biUnion id)).card ≤ (Bs.biUnion id).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ Bs.card * L + 1 := Nat.add_le_add_right (hbi.trans hsum) 1
    _ ≤ Fintype.card (RuleSetVertex {w}) * L + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right L hblocks) 1
    _ = 1 + L * Fintype.card (RuleSetVertex {w}) := by
      simp only [Nat.mul_comm, Nat.add_comm]
end DeletionCode.AttachedBlocks
