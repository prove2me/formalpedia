-- Prove2me | solution 1 for DeletionCode.Windows.insertion_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:29.815303+00:00
-- url     : https://prove2.me/submissions/756b7492-4967-4534-b93e-a5b6fd5d886b

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ) (d : Bool)
    (h : s + k ≤ ell) : Agree (insertAt p ell d) s p s k := by
  intro i hi
  have hidx : s + i < ell := by omega
  simp [insertAt, hidx]
end DeletionCode.Windows
