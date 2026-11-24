-- Prove2me | solution 1 for BB6Kit.kit_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:14:10.51651+00:00
-- url     : https://prove2.me/submissions/b886a3e9-2dd5-479c-bf92-44b5000515f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_indep_or_smooth
import Theorems.Thm_BB6Kit_degenerate
import Theorems.Thm_BB6Kit_nondegenerate

theorem solution (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  rcases BB6Kit.indep_or_smooth c hc with h | h
  · exact BB6Kit.nondegenerate i k c hi hc hc4 hk2 hk hne h
  · exact BB6Kit.degenerate i k c hi hc hc4 hk2 hk hne h
