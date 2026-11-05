-- Prove2me | solution 1 for ClauseBound.Rec.pow_mul_sum_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:34:24.059208+00:00
-- url     : https://prove2.me/submissions/920c1013-4aa6-4384-9be9-463c909ae28b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ClauseBound_Rec_Few

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset
namespace ClauseBound.Rec
theorem _root_.solution {δ n : ℕ} (h2 : n ≤ δ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y ^ n * ∑ ν ∈ range (n + 1), (δ.choose ν : ℝ) ≤ (y + 1) ^ δ := by
  rw [add_pow, mul_sum]
  calc ∑ ν ∈ range (n + 1), y ^ n * (δ.choose ν : ℝ) ≤ ∑ ν ∈ range (n + 1), y ^ ν * 1 ^ (δ - ν) * (δ.choose ν : ℝ) := by
        refine sum_le_sum fun ν hν => ?_
        rw [one_pow, mul_one]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hy0 hy1 (by simpa [Nat.lt_succ_iff] using hν)) (by positivity)
    _ ≤ ∑ ν ∈ range (δ + 1), y ^ ν * 1 ^ (δ - ν) * (δ.choose ν : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun ν _ _ => by positivity
end ClauseBound.Rec
