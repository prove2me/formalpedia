-- Prove2me | solution 1 for Finset.sum_shift_back
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:59:02.148798+00:00
-- url     : https://prove2.me/submissions/54758f3f-8ec9-4141-8148-b9406ed1f4f5

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open BigOperators

theorem solution {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]
