-- Prove2me | solution 1 for DeletionCode.Windows.bubble_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:37.558956+00:00
-- url     : https://prove2.me/submissions/05e53adb-8adf-4e21-a8f4-81b344ab4659

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (k ρ : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1) :
    let L := 3 * (k + 1)
    L - ρ < L ∧ L - ρ - 1 < L ∧
    k + 1 < 2 * L - ρ - 1 ∧ (L - 1) + k < 2 * L - ρ := by
  dsimp
  omega
end DeletionCode.Windows
