-- Prove2me | solution 2 for BroughanRH.chebyshev
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:17.525823+00:00
-- url     : https://prove2.me/submissions/7af86809-ff96-4395-9bf6-bf6e052d0152
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis

theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 :=
  LandauCriterion.psi_error_of_riemannHypothesis mathlib_riemannHypothesis
