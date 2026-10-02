-- Prove2me | solution 1 for DiophantineQuintuple.case2_certified_b_lower
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:23:40.140987+00:00
-- url     : https://prove2.me/submissions/e31e9e47-ac39-496b-a23c-a7d03e0c2a1e

import Mathlib

/-! Disproof of 558cc6a4 `DiophantineQuintuple.case2_certified_b_lower`.
The formal statement carries no Diophantine-quintuple hypothesis: it claims every `b` with
`2a ≤ b ≤ 8a` and `0 < a` exceeds 130000. Take `a = 1`, `b = 2`. -/

theorem solution : ¬ (∀ (a b : Nat) (ha : 0 < a)
    (h1 : 2 * a ≤ b) (h2 : b ≤ 8 * a),
    130000 < b) := by
  intro h
  have := h 1 2 (by norm_num) (by norm_num) (by norm_num)
  omega
