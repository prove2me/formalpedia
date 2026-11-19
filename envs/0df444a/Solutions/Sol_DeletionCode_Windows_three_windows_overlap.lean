-- Prove2me | solution 1 for DeletionCode.Windows.three_windows_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:58:49.548985+00:00
-- url     : https://prove2.me/submissions/c7b85bda-d4f2-4558-a7f7-10e33bd89c11

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (k D : ℕ) (hD : D < 3 * (k + 1)) :
    D / 2 + k ≤ 3 * (k + 1) ∧
    (D - D / 2) + k ≤ 3 * (k + 1) := by omega
end DeletionCode.Windows
