-- Prove2me | solution 1 for FormalCapacity.Finite.threeLabel_stability
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T21:59:54.713969+00:00
-- url     : https://prove2.me/submissions/634d64ca-4e2e-4e24-86ff-33e4f2341ecc

import Mathlib
import Definitions.Def_capacityThreeLabel

set_option autoImplicit false

/-!
# The three-label scalar stability inequality

This file formalizes the finite, pointwise heart of the temporal capacity-flow
argument.  It contains no measure theory and no stochastic assumptions.

The variables `beta123`, `beta12`, `beta23`, and `beta13` are nonnegative
block intensities at one density point.  The three `cap` assumptions say that
the blocks using a label cannot exceed that label's available density.  The
`dij` variables are the pairwise maximality deficits.
-/

namespace FormalCapacity.Finite











lemma canonical123_add_canonical12 (f1 f2 f3 : ℝ) :
    canonical123 f1 f2 f3 + canonical12 f1 f2 f3 = min f1 f2 := by
  rw [canonical123, canonical12, ← min_assoc]
  rcases le_total (min f1 f2) f3 with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma canonical123_add_canonical23 (f1 f2 f3 : ℝ) :
    canonical123 f1 f2 f3 + canonical23 f1 f2 f3 = min f2 f3 := by
  rw [canonical123, canonical23]
  rcases le_total (min f2 f3) f1 with h | h
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma canonical123_eq_endpoint_min
    {f1 f2 f3 : ℝ} (hmiddle : min f1 f3 ≤ f2) :
    canonical123 f1 f2 f3 = min f1 f3 := by
  rcases le_total f1 f3 with h13 | h31
  · have h12 : f1 ≤ f2 := by
      rw [min_eq_left h13] at hmiddle
      exact hmiddle
    rw [canonical123, min_eq_left (le_min h12 h13), min_eq_left h13]
  · have h32 : f3 ≤ f2 := by
      rw [min_eq_right h31] at hmiddle
      exact hmiddle
    rw [canonical123, min_eq_right h32, min_eq_right h31]



end FormalCapacity.Finite


/-!
# The three-label scalar stability inequality

This file formalizes the finite, pointwise heart of the temporal capacity-flow
argument.  It contains no measure theory and no stochastic assumptions.

The variables `beta123`, `beta12`, `beta23`, and `beta13` are nonnegative
block intensities at one density point.  The three `cap` assumptions say that
the blocks using a label cannot exceed that label's available density.  The
`dij` variables are the pairwise maximality deficits.
-/

open FormalCapacity.Finite

theorem solution
    {f1 f2 f3 beta123 beta12 beta23 beta13 d12 d23 d13 q12 q23 : ℝ}
    (_hbeta123 : 0 ≤ beta123)
    (hbeta12 : 0 ≤ beta12)
    (hbeta23 : 0 ≤ beta23)
    (hbeta13 : 0 ≤ beta13)
    (hcap1 : beta123 + beta12 + beta13 ≤ f1)
    (hcap2 : beta123 + beta12 + beta23 ≤ f2)
    (hcap3 : beta123 + beta13 + beta23 ≤ f3)
    (hd12 : d12 = min f1 f2 - beta123 - beta12)
    (hd23 : d23 = min f2 f3 - beta123 - beta23)
    (hd13 : d13 = min f1 f3 - beta123 - beta13)
    (_hq12_nonneg : 0 ≤ q12)
    (hq12_le_one : q12 ≤ 1)
    (_hq23_nonneg : 0 ≤ q23)
    (hq23_le_one : q23 ≤ 1)
    (hq_sum : 1 ≤ q12 + q23)
    (hmiddle : min f1 f3 ≤ f2) :
    canonicalScore q12 q23 f1 f2 f3 - d12 - d23 ≤
        threeScore q12 q23 beta123 beta12 beta23 ∧
      threeScore q12 q23 beta123 beta12 beta23 ≤
        canonicalScore q12 q23 f1 f2 f3 + d13 := by
  have hb12_le_f1 : beta123 + beta12 ≤ f1 := by linarith
  have hb12_le_f2 : beta123 + beta12 ≤ f2 := by linarith
  have hb23_le_f2 : beta123 + beta23 ≤ f2 := by linarith
  have hb23_le_f3 : beta123 + beta23 ≤ f3 := by linarith
  have hb13_le_f1 : beta123 + beta13 ≤ f1 := by linarith
  have hb13_le_f3 : beta123 + beta13 ≤ f3 := by linarith
  have hd12_nonneg : 0 ≤ d12 := by
    rw [hd12]
    have := le_min hb12_le_f1 hb12_le_f2
    linarith
  have hd23_nonneg : 0 ≤ d23 := by
    rw [hd23]
    have := le_min hb23_le_f2 hb23_le_f3
    linarith
  have hd13_nonneg : 0 ≤ d13 := by
    rw [hd13]
    have := le_min hb13_le_f1 hb13_le_f3
    linarith

  let gamma123 := canonical123 f1 f2 f3
  let gamma12 := canonical12 f1 f2 f3
  let gamma23 := canonical23 f1 f2 f3
  let D : ℝ → ℝ → ℝ := fun u v =>
    threeScore u v beta123 beta12 beta23 -
      threeScore u v gamma123 gamma12 gamma23

  have hD10 : D 1 0 = -d12 := by
    dsimp [D, threeScore, gamma123, gamma12, gamma23]
    simp only [one_mul, zero_mul, add_zero]
    rw [canonical123_add_canonical12]
    linarith
  have hD01 : D 0 1 = -d23 := by
    dsimp [D, threeScore, gamma123, gamma12, gamma23]
    simp only [one_mul, zero_mul, add_zero]
    rw [canonical123_add_canonical23]
    linarith

  have hbeta123_le_gamma123 : beta123 ≤ gamma123 := by
    dsimp [gamma123, canonical123]
    rw [le_min_iff, le_min_iff]
    constructor
    · linarith
    · constructor <;> linarith

  have hD11_formula : D 1 1 = gamma123 - beta123 - d12 - d23 := by
    dsimp [D, threeScore, gamma123, gamma12, gamma23]
    have h12 := canonical123_add_canonical12 f1 f2 f3
    have h23 := canonical123_add_canonical23 f1 f2 f3
    linarith

  have hdelta_upper : gamma123 - beta123 ≤ d12 + d23 + d13 := by
    rcases le_total f1 f3 with h13 | h31
    · have h12 : f1 ≤ f2 := by
        have : min f1 f3 = f1 := min_eq_left h13
        linarith
      have hg : gamma123 = f1 := by
        dsimp [gamma123]
        rw [canonical123_eq_endpoint_min hmiddle, min_eq_left h13]
      have hm12 : min f1 f2 = f1 := min_eq_left h12
      have hm13 : min f1 f3 = f1 := min_eq_left h13
      rw [hg, hd12, hd13, hm12, hm13]
      linarith
    · have h32 : f3 ≤ f2 := by
        have : min f1 f3 = f3 := min_eq_right h31
        linarith
      have hg : gamma123 = f3 := by
        dsimp [gamma123]
        rw [canonical123_eq_endpoint_min hmiddle, min_eq_right h31]
      have hm23 : min f2 f3 = f3 := min_eq_right h32
      have hm13 : min f1 f3 = f3 := min_eq_right h31
      rw [hg, hd23, hd13, hm23, hm13]
      linarith

  have hD10_lower : -d12 - d23 ≤ D 1 0 := by rw [hD10]; linarith
  have hD01_lower : -d12 - d23 ≤ D 0 1 := by rw [hD01]; linarith
  have hD11_lower : -d12 - d23 ≤ D 1 1 := by
    rw [hD11_formula]
    linarith
  have hD10_upper : D 1 0 ≤ d13 := by rw [hD10]; linarith
  have hD01_upper : D 0 1 ≤ d13 := by rw [hD01]; linarith
  have hD11_upper : D 1 1 ≤ d13 := by
    rw [hD11_formula]
    linarith

  let lambda10 := 1 - q23
  let lambda01 := 1 - q12
  let lambda11 := q12 + q23 - 1
  have hlambda10 : 0 ≤ lambda10 := by dsimp [lambda10]; linarith
  have hlambda01 : 0 ≤ lambda01 := by dsimp [lambda01]; linarith
  have hlambda11 : 0 ≤ lambda11 := by dsimp [lambda11]; linarith
  have hlambda_sum : lambda10 + lambda01 + lambda11 = 1 := by
    dsimp [lambda10, lambda01, lambda11]
    ring
  have hD_decomp :
      D q12 q23 = lambda10 * D 1 0 + lambda01 * D 0 1 + lambda11 * D 1 1 := by
    dsimp [D, threeScore, lambda10, lambda01, lambda11]
    ring

  have hD_lower : -d12 - d23 ≤ D q12 q23 := by
    rw [hD_decomp]
    have h10 := mul_le_mul_of_nonneg_left hD10_lower hlambda10
    have h01 := mul_le_mul_of_nonneg_left hD01_lower hlambda01
    have h11 := mul_le_mul_of_nonneg_left hD11_lower hlambda11
    nlinarith [hlambda_sum]
  have hD_upper : D q12 q23 ≤ d13 := by
    rw [hD_decomp]
    have h10 := mul_le_mul_of_nonneg_left hD10_upper hlambda10
    have h01 := mul_le_mul_of_nonneg_left hD01_upper hlambda01
    have h11 := mul_le_mul_of_nonneg_left hD11_upper hlambda11
    nlinarith [hlambda_sum]

  change canonicalScore q12 q23 f1 f2 f3 - d12 - d23 ≤
      threeScore q12 q23 beta123 beta12 beta23 ∧
    threeScore q12 q23 beta123 beta12 beta23 ≤
      canonicalScore q12 q23 f1 f2 f3 + d13
  dsimp [canonicalScore]
  constructor
  · dsimp [D, gamma123, gamma12, gamma23] at hD_lower
    linarith
  · dsimp [D, gamma123, gamma12, gamma23] at hD_upper
    linarith
