-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcut_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:56.800538+00:00
-- url     : https://prove2.me/submissions/7654ce7e-981c-48d0-a3e6-e24a7d9f58bd

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Theorems.Thm_FirstPassageLinearTransport_modEq_of_two_mul

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {H n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ (H + 1)]) :
    shortcut n ≡ shortcut n' [MOD 2 ^ H] := by
  have hdvd : (2 : ℕ) ∣ 2 ^ (H + 1) :=
    dvd_pow_self 2 (Nat.succ_ne_zero H)
  have h2 : n % 2 = n' % 2 := h.of_dvd hdvd
  apply modEq_of_two_mul
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hn' : n' % 2 = 0 := by omega
    rw [two_mul_shortcut_of_even hn, two_mul_shortcut_of_even hn']
    exact h
  · have hn' : n' % 2 = 1 := by omega
    rw [two_mul_shortcut_of_odd hn, two_mul_shortcut_of_odd hn']
    exact Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 h)
end FirstPassageLinearTransport
