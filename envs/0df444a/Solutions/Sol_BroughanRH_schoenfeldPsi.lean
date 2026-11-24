-- Prove2me | solution 1 for BroughanRH.schoenfeldPsi
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:25:35.689545+00:00
-- url     : https://prove2.me/submissions/3f3917bf-588b-48c9-88fa-1407ef16f1e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_SchoenfeldBRH_psi_bound_large_of_RH_low_count
import Theorems.Thm_SchoenfeldBRH_zero_count_upper_low_heights
import Theorems.Thm_SchoenfeldBRH_psi_bound_finite_range

theorem solution :
    ∀ x : ℝ, (73.2 : ℝ) ≤ x → |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) := by
  intro x hx
  rcases le_or_gt x (Real.exp 13) with h | h
  · exact SchoenfeldBRH.psi_bound_finite_range x hx h
  · exact SchoenfeldBRH.psi_bound_large_of_RH_low_count riemann_hypothesis
      SchoenfeldBRH.zero_count_upper_low_heights x h.le
