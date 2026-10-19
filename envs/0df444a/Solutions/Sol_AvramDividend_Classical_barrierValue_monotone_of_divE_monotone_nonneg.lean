-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_monotone_of_divE_monotone_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:21:38.926826+00:00
-- url     : https://prove2.me/submissions/9a052042-fa20-443b-a4a4-d1983fa10e2b

import Mathlib
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hm : MonotoneOn (fun z : ℝ => divE (W z) (scaleDeriv W a)) (Ici 0))
    (hn : ∀ z : ℝ, 0 ≤ z → 0 ≤ divE (W z) (scaleDeriv W a)) :
    Monotone (barrierValue W a) := by
  intro x y hxy
  have hga : 0 ≤ divE (W a) (scaleDeriv W a) := hn a ha
  unfold barrierValue
  by_cases hy : y < 0
  · have hx : x < 0 := lt_of_le_of_lt hxy hy
    simp [hx, hy]
  · by_cases hx : x < 0
    · rw [if_pos hx, if_neg hy]
      split_ifs with h
      · exact hn y (not_lt.1 hy)
      · linarith
    · rw [if_neg hx, if_neg hy]
      have hx0 : 0 ≤ x := not_lt.1 hx
      have hy0 : 0 ≤ y := not_lt.1 hy
      split_ifs with h1 h2 h2
      · exact hm (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hy0) hxy
      · have := hm (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 ha) h1
        linarith
      · linarith
      · linarith
