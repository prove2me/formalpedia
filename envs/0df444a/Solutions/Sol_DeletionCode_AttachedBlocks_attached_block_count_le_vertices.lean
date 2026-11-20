-- Prove2me | solution 1 for DeletionCode.AttachedBlocks.attached_block_count_le_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:37.257307+00:00
-- url     : https://prove2.me/submissions/3a03c76d-0b55-490f-ae13-7543e61e7088

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators
namespace DeletionCode.AttachedBlocks
theorem _root_.solution {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    Bs.card ≤ Fintype.card (RuleSetVertex {w}) := by
  classical
  let chooseVertex : Bs → RuleSetVertex {w} := fun B =>
    ⟨Classical.choose (hmeet B.val B.property),
      (Classical.choose_spec (hmeet B.val B.property)).2⟩
  have hbelongs (B : Bs) : Incident B.val (chooseVertex B).val :=
    (Classical.choose_spec (hmeet B.val B.property)).1
  have hinj : Function.Injective chooseVertex := by
    intro B C heq
    apply Subtype.ext
    by_contra hne
    have hvertices : (chooseVertex B).val = (chooseVertex C).val :=
      congrArg Subtype.val heq
    have hC : Incident C.val (chooseVertex B).val := by
      rw [hvertices]
      exact hbelongs C
    exact hdisjoint B.val B.property C.val C.property hne
      (chooseVertex B).val (hbelongs B) hC
  simpa using Fintype.card_le_of_injective chooseVertex hinj
end DeletionCode.AttachedBlocks
