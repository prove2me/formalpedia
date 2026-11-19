-- Prove2me | solution 1 for DeletionCode.Windows.three_windows_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:58:45.202072+00:00
-- url     : https://prove2.me/submissions/85c8b7de-5224-4689-8a56-420f60011137

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution
    (k D s : ℕ) (hD : D < 3 * (k + 1))
    (hs : s + k ≤ 3 * (k + 1) + D) :
    ∃ a : ℕ, (a = 0 ∨ a = D / 2 ∨ a = D) ∧
      a ≤ s ∧ s + k ≤ a + 3 * (k + 1) := by
  by_cases hfirst : s + k ≤ 3 * (k + 1)
  · exact ⟨0, Or.inl rfl, Nat.zero_le s, by omega⟩
  · by_cases hmiddle : s + k ≤ D / 2 + 3 * (k + 1)
    · exact ⟨D / 2, Or.inr (Or.inl rfl), by omega, hmiddle⟩
    · exact ⟨D, Or.inr (Or.inr rfl), by omega, by omega⟩
end DeletionCode.Windows
