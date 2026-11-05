-- Prove2me | solution 1 for ClauseBound.Rec.sum_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:46.440411+00:00
-- url     : https://prove2.me/submissions/66aa917a-94c2-4c71-abbb-cc2d4e462d00

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
import Theorems.Thm_ClauseBound_Rec_pow_mul_sum_choose_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset
namespace ClauseBound.Rec
theorem _root_.solution {δ n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ δ) :
    (∑ ν ∈ range (n + 1), (δ.choose ν : ℝ)) ≤ (3 * δ / n) ^ n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h1
  have hδ : (0 : ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hy0 : (0 : ℝ) < n / δ := by positivity
  have hy1 : (n : ℝ) / δ ≤ 1 := (div_le_one hδ).2 (by exact_mod_cast h2)
  have h3 : ((n : ℝ) / δ + 1) ^ δ ≤ 3 ^ n := by
    calc ((n : ℝ) / δ + 1) ^ δ ≤ Real.exp ((n : ℝ) / δ) ^ δ := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp 1 ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one, mul_div_cancel₀ _ hδ.ne']
      _ ≤ 3 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
  have h4 := (pow_mul_sum_choose_le h2 hy0.le hy1).trans h3
  have h5 : (3 * (δ : ℝ) / n) ^ n = 3 ^ n / ((n : ℝ) / δ) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [h5, le_div_iff₀ (by positivity), mul_comm]
  exact h4
end ClauseBound.Rec
