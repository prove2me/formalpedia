-- Prove2me | solution 1 for DerivativeChainContinuation.positive_power_midpoint_strict
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:28:17.01155+00:00
-- url     : https://prove2.me/submissions/598bebc0-844b-45f5-b06d-8e82c7f7af0e

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (k : ℕ) (hk : 2≤k) (a b x : ℝ)
    (ha : 0≤a) (hab : a<b) (hx : 0≤x)
    (hmid : (a^k+b^k)/2≤x^k) : (a+b)/2<x := by
  have hconv := (strictConvexOn_pow hk).2 ha (by linarith : 0≤b) (ne_of_lt hab)
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hpow : ((a+b)/2)^k<x^k := by
    have hcv : ((a+b)/2)^k<(a^k+b^k)/2 := by
      simp only [smul_eq_mul] at hconv
      have hl : (a+b)/2=(1/2 : ℝ)*a+(1/2 : ℝ)*b := by ring
      have hr : (a^k+b^k)/2=(1/2 : ℝ)*a^k+(1/2 : ℝ)*b^k := by ring
      rw [hl,hr]
      exact hconv
    exact hcv.trans_le hmid
  by_contra hn
  have hle : x≤(a+b)/2 := le_of_not_gt hn
  have hp := pow_le_pow_left₀ hx hle k
  exact (not_lt_of_ge hp) hpow
