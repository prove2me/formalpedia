-- Prove2me | solution 1 for FirstPassageLinearTransport.two_mul_shortcut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:09.0448+00:00
-- url     : https://prove2.me/submissions/0b4be901-583f-4a90-92fa-eaba10a0700b

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
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
theorem _root_.solution (n : ℕ) :
    2 * shortcut n = 3 ^ (n % 2) * n + n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · simp [hn, two_mul_shortcut_of_even hn]
  · simp [hn, two_mul_shortcut_of_odd hn]
end FirstPassageLinearTransport
