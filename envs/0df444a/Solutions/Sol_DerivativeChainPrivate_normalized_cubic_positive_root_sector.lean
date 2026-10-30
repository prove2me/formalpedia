-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cubic_positive_root_sector
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:30:23.66499+00:00
-- url     : https://prove2.me/submissions/4cbcaf91-99e1-4699-973e-40094064cf18

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (β z : ℂ)
    (hβre : 0 ≤ β.re) (hβim : 0 ≤ β.im)
    (hz : z ^ 3 - z = β) (hzre : 0 < z.re) :
    1 ≤ z.re ∧ 0 ≤ z.im ∧ 1 + 3 * z.im ^ 2 ≤ z.re ^ 2 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hre him
  have hprod : 0 ≤ z.re * (z.re ^ 2 - 3 * z.im ^ 2 - 1) := by
    nlinarith only [hre, hβre]
  have hsector : 1 + 3 * z.im ^ 2 ≤ z.re ^ 2 := by
    have h := nonneg_of_mul_nonneg_right hprod hzre
    linarith
  have hcoeff : 0 < 3 * z.re ^ 2 - z.im ^ 2 - 1 := by
    nlinarith only [hsector, sq_nonneg z.im]
  have himprod : 0 ≤ z.im * (3 * z.re ^ 2 - z.im ^ 2 - 1) := by
    nlinarith only [him, hβim]
  exact ⟨by nlinarith only [hsector, sq_nonneg z.im, hzre],
    nonneg_of_mul_nonneg_left himprod hcoeff, hsector⟩
