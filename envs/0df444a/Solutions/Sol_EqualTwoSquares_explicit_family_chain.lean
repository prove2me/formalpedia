-- Prove2me | solution 1 for EqualTwoSquares.explicit_family_chain
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:18.41395+00:00
-- url     : https://prove2.me/submissions/3f83e867-89fb-4efd-a6ce-576fe8ee1ec6

-- Public-mission submission for EqualTwoSquares.explicit_family_chain.

import Mathlib

theorem solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith
