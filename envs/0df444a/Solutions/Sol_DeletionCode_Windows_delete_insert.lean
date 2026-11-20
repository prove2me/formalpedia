-- Prove2me | solution 1 for DeletionCode.Windows.delete_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:18.848385+00:00
-- url     : https://prove2.me/submissions/dde9a4f6-ca3a-47f3-885d-43ce84d8f5c8

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell : ℕ) (d : Bool) :
    deleteAt (insertAt p ell d) ell = p := by
  funext i
  by_cases h : i < ell
  · simp [deleteAt, insertAt, h]
  · have hnext : ¬ i + 1 < ell := by omega
    have hne : i + 1 ≠ ell := by omega
    simp [deleteAt, insertAt, h, hnext, hne]
end DeletionCode.Windows
