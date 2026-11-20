-- Prove2me | solution 1 for DeletionCode.AttachedBlocks.attached_union_card_bound_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:30.968043+00:00
-- url     : https://prove2.me/submissions/9e1d06b8-287a-4e13-884d-b25700f53eab

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks
import Theorems.Thm_DeletionCode_AttachedBlocks_attached_union_card_bound

set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators
namespace DeletionCode.AttachedBlocks
theorem _root_.solution {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 4 * t * L) :
    (insert w (Bs.biUnion id)).card ≤ 1 + 4 * t * L ^ 2 := by
  calc
    (insert w (Bs.biUnion id)).card ≤ 1 + L * Fintype.card (RuleSetVertex {w}) :=
      attached_union_card_bound Bs w L hsize hmeet hdisjoint
    _ ≤ 1 + L * (4 * t * L) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left L hvertices) 1
    _ = 1 + 4 * t * L ^ 2 := by
      simp only [pow_two]
      ac_rfl
end DeletionCode.AttachedBlocks
