-- Prove2me | solution 1 for BroughanRH.schoenfeldBook
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:47:19.344798+00:00
-- url     : https://prove2.me/submissions/2cae9811-6ef8-4fee-bf81-1800e641e108
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_schoenfeldPsi
import Mathlib

theorem solution :
    ∀ x : ℝ, 74 ≤ x → |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) := by
  intro x hx
  exact (BroughanRH.schoenfeldPsi x (by norm_num at hx ⊢; linarith)).le
