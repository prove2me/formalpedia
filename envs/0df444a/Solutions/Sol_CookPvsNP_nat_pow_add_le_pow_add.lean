-- Prove2me | solution 1 for CookPvsNP.nat_pow_add_le_pow_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T07:12:59.431984+00:00
-- url     : https://prove2.me/submissions/ec4ef436-6e43-4011-8f4d-5162e2bd706b

import Mathlib
import Definitions.Def_CookPvsNP_defs

open CookPvsNP

theorem solution (n a c : ℕ) :
    n ^ a + c ≤ n ^ (a + c + 2) + (a + c + 2) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    cases a <;> simp <;> omega
  · have hp : n ^ a ≤ n ^ (a + c + 2) := Nat.pow_le_pow_right hn (by omega)
    omega
