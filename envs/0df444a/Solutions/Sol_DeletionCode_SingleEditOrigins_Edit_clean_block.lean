-- Prove2me | solution 1 for DeletionCode.SingleEditOrigins.Edit.clean_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:15.893583+00:00
-- url     : https://prove2.me/submissions/cfa3d6a6-c203-41fe-85bb-dcaf13cdc364

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_SingleEditOrigins

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditOrigins
open Windows
open DeletionCode.SingleEditOrigins.Edit
namespace DeletionCode.SingleEditOrigins.Edit
theorem _root_.solution (e : Edit) (a s k : ℕ)
    (h : a + s + k ≤ e.cut ∨ e.cut < a + s) :
    ∃ r, ∀ i, i < k → e.origin (a + s + i) = some (r + i) := by
  cases e with
  | unchanged => exact ⟨a + s, fun _ _ => rfl⟩
  | delete pos =>
    rcases h with hbefore | hafter
    · change a + s + k ≤ pos at hbefore
      refine ⟨a + s, ?_⟩
      intro i hi
      have hcut : a + s + i < pos := by omega
      simp only [origin, if_pos hcut]
    · change pos < a + s at hafter
      refine ⟨a + s + 1, ?_⟩
      intro i hi
      have hcut : ¬ a + s + i < pos := by omega
      have heq : a + s + i + 1 = a + s + 1 + i := by omega
      simp only [origin, if_neg hcut, heq]
  | insert pos bit =>
    rcases h with hbefore | hafter
    · change a + s + k ≤ pos at hbefore
      refine ⟨a + s, ?_⟩
      intro i hi
      have hcut : a + s + i < pos := by omega
      simp only [origin, if_pos hcut]
    · change pos < a + s at hafter
      refine ⟨a + s - 1, ?_⟩
      intro i hi
      have hcut : ¬ a + s + i < pos := by omega
      have hne : a + s + i ≠ pos := by omega
      have heq : a + s + i - 1 = a + s - 1 + i := by omega
      simp only [origin, if_neg hcut, if_neg hne, heq]
end DeletionCode.SingleEditOrigins.Edit
