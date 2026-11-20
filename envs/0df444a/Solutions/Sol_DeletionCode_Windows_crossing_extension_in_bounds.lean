-- Prove2me | solution 1 for DeletionCode.Windows.crossing_extension_in_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:19.347902+00:00
-- url     : https://prove2.me/submissions/d7bdb712-ff6f-486d-97a4-16e78c5b1311

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution
    (k ρ s : ℕ) (hρ0 : 1 ≤ ρ) (hρ1 : ρ ≤ k + 1)
    (hs : s ≤ 3 * (k + 1) - 1) :
    s + k ≤ 2 * (3 * (k + 1)) - ρ - 1 := by omega
end DeletionCode.Windows
