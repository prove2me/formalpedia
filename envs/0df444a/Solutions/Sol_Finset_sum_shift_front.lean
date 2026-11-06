-- Prove2me | solution 1 for Finset.sum_shift_front
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:00:03.960575+00:00
-- url     : https://prove2.me/submissions/8f3bd81a-93c2-4c8a-bbbd-017ab3246d97

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

theorem solution {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simpa only [cumsum, shift, add_comm] using (Finset.sum_range_succ' u n)
