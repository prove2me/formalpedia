-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:35.374909+00:00
-- url     : https://prove2.me/submissions/0f70725b-be37-43a1-9e5f-3145a8ad0668

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_shortcut_modEq
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ i j n n' : ℕ, n ≡ n' [MOD 2 ^ (i + j)] →
      orbit i n ≡ orbit i n' [MOD 2 ^ j] := by
  intro i
  induction i with
  | zero =>
      intro j n n' h
      simpa using h
  | succ i ih =>
      intro j n n' h
      rw [orbit_succ, orbit_succ]
      apply shortcut_modEq
      apply ih
      rwa [show i + (j + 1) = i + 1 + j by omega]
end FirstPassageLinearTransport
