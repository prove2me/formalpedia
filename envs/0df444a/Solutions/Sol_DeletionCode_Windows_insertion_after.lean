-- Prove2me | solution 1 for DeletionCode.Windows.insertion_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:36.648789+00:00
-- url     : https://prove2.me/submissions/d4f6d6df-aedc-426b-a5fb-3ae6a2b1e827

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ) (d : Bool)
    (h : ell ≤ s) : Agree (insertAt p ell d) (s + 1) p s k := by
  intro i hi
  have hlt : ¬ s + 1 + i < ell := by omega
  have hne : s + 1 + i ≠ ell := by omega
  have hidx : s + 1 + i - 1 = s + i := by omega
  simp [insertAt, hlt, hne, hidx]
end DeletionCode.Windows
