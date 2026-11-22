-- Prove2me | solution 2 for BroughanRH.primeCounting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:18.453157+00:00
-- url     : https://prove2.me/submissions/116b44e5-ad1b-4141-a469-e77dd9d6e62a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis

theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x :=
  VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis mathlib_riemannHypothesis
