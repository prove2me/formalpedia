-- Prove2me | solution 1 for DeletionCode.TwoEditWindows.candidate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:08.803674+00:00
-- url     : https://prove2.me/submissions/28ca9457-de16-4442-a8cf-953a5c8b67c6

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows

set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows
namespace DeletionCode.TwoEditWindows
theorem _root_.solution {k s : ℕ}
    (hs : s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) : s + k ≤ 3 * k + 2 := by
  rcases hs with rfl | rfl | rfl <;> omega
end DeletionCode.TwoEditWindows
