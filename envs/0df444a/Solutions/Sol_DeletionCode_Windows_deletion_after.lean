-- Prove2me | solution 1 for DeletionCode.Windows.deletion_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:18.58916+00:00
-- url     : https://prove2.me/submissions/c5f0dd80-0b40-4525-91d0-a794f053e01f

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ)
    (h : ell < s) : Agree (deleteAt p ell) (s - 1) p s k := by
  intro i hi
  have hidx : ¬ s - 1 + i < ell := by omega
  have heq : s - 1 + i + 1 = s + i := by omega
  simp [deleteAt, hidx, heq]
end DeletionCode.Windows
