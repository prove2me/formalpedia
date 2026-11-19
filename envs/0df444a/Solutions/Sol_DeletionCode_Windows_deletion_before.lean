-- Prove2me | solution 1 for DeletionCode.Windows.deletion_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:10:23.537854+00:00
-- url     : https://prove2.me/submissions/43f12da3-a1e1-41c8-9856-99975a64d627

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ)
    (h : s + k ≤ ell) : Agree (deleteAt p ell) s p s k := by
  intro i hi
  have hidx : s + i < ell := by omega
  simp [deleteAt, hidx]
end DeletionCode.Windows
