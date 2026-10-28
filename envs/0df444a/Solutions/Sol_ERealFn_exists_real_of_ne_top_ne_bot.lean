-- Prove2me | solution 1 for ERealFn.exists_real_of_ne_top_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:37.553107+00:00
-- url     : https://prove2.me/submissions/8f536c21-28d4-4915-a48b-3a4477d46202

import Mathlib

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 46-47

theorem solution {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) :
    ∃ r : ℝ, e = r := by
  exact ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩
