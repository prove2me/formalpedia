-- Prove2me | solution 1 for DeletionCode.Windows.insert_delete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:07:36.038473+00:00
-- url     : https://prove2.me/submissions/7a7f0ec4-d809-496c-995c-3c7caa3f74c1

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell : ℕ) :
    insertAt (deleteAt p ell) ell (p ell) = p := by
  funext i
  by_cases h : i < ell
  · simp [insertAt, deleteAt, h]
  · by_cases heq : i = ell
    · subst i
      simp [insertAt]
    · have hprev : ¬ i - 1 < ell := by omega
      have hidx : i - 1 + 1 = i := by omega
      simp [insertAt, deleteAt, h, heq, hprev, hidx]
end DeletionCode.Windows
