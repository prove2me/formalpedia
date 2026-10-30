-- Prove2me | solution 1 for DerivativeChainContinuation.sqrt_transport_constant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:09:04.155888+00:00
-- url     : https://prove2.me/submissions/92ba8fea-fb3f-422f-acba-8a5f09545d63

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


theorem solution (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x+2)+4*Real.sqrt (x+1)-4*Real.sqrt 2 ≤ 5*Real.sqrt x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have h2 : Real.sqrt (x+2) ≤ Real.sqrt x+Real.sqrt 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : 0≤x+2)]
    nlinarith [Real.sq_sqrt hx, mul_nonneg (Real.sqrt_nonneg x) hp]
  have h1 : Real.sqrt (x+1) ≤ Real.sqrt x+1 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity : 0≤x+1)]
    nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg x]
  nlinarith
