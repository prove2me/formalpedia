-- Prove2me | solution 1 for FirstPassageLinearTransport.modEq_of_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:19.791451+00:00
-- url     : https://prove2.me/submissions/7ff0dc19-f680-4513-beff-a87a32c32cc4

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {H a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ (H + 1)]) :
    a ≡ b [MOD 2 ^ H] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  push_cast at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hp : ((2 : ℤ)) ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [hp] at hk
  linarith
end FirstPassageLinearTransport
