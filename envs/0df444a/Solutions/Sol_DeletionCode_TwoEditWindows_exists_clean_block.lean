-- Prove2me | solution 1 for DeletionCode.TwoEditWindows.exists_clean_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:45.949821+00:00
-- url     : https://prove2.me/submissions/219b55c8-fa67-445a-ab8c-c3d6b0348573

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
import Theorems.Thm_DeletionCode_TwoEditWindows_exists_clean_block_among_three

set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows
namespace DeletionCode.TwoEditWindows
theorem _root_.solution (k a b p q : ℕ) :
    ∃ s : ℕ, s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by
  obtain ⟨s, _, hbound, ha, hb⟩ := exists_clean_block_among_three k a b p q
  exact ⟨s, hbound, ha, hb⟩
end DeletionCode.TwoEditWindows
