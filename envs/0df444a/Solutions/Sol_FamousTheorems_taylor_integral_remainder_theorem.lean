-- Prove2me | solution 1 for FamousTheorems.taylor_integral_remainder_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:29:12.756573+00:00
-- url     : https://prove2.me/submissions/ba2b4268-a556-46b7-9c94-d06faf7df108

import Mathlib

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.uIcc x₀ x)) :
    f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / (n.factorial : ℝ)) • iteratedDerivWithin (n + 1) f (Set.uIcc x₀ x) t :=
  taylor_integral_remainder hf
