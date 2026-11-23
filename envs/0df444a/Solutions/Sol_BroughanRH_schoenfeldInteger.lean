-- Prove2me | solution 1 for BroughanRH.schoenfeldInteger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:47:20.40397+00:00
-- url     : https://prove2.me/submissions/2fba622f-3e2b-4acb-ae69-173438e264f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_schoenfeldPsi
import Mathlib

theorem solution :
    ∀ n : ℕ, 600 ≤ n → |Chebyshev.psi n - (n : ℝ)| < Real.sqrt n * (Real.log n)^2 := by
  intro n hn
  have hx : (73.2 : ℝ) ≤ (n : ℝ) := by
    have : (600 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num; linarith
  have h := BroughanRH.schoenfeldPsi (n : ℝ) hx
  have hA : 0 ≤ Real.sqrt n * (Real.log n)^2 := by positivity
  have hpi : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc |Chebyshev.psi n - (n : ℝ)| < Real.sqrt n * (Real.log n)^2 / (8 * Real.pi) := h
    _ ≤ Real.sqrt n * (Real.log n)^2 := div_le_self hA hpi
