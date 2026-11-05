-- Prove2me | solution 1 for ClauseBound.Rec.abs_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:51.498355+00:00
-- url     : https://prove2.me/submissions/2808d0dd-2fe5-4814-bfe7-8af2a30dd179

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
import Definitions.Def_PiecesStatement
import Definitions.Def_ClauseBound_Rec_Window

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset
namespace ClauseBound.Rec
theorem _root_.solution (a : ℤ) (k : ℕ) : |Ring.choose a k| ≤ 2 ^ (a.natAbs + k) := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Ring.choose_natCast, Int.natAbs_natCast, abs_of_nonneg (by positivity)]
    calc ((n.choose k : ℕ) : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast Nat.choose_le_two_pow n k
      _ ≤ 2 ^ (n + k) := by push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (a := -a - 1) (by omega)
    obtain rfl : a = -((n : ℤ) + 1) := by omega
    rw [Ring.choose_neg, show (n : ℤ) + 1 + k - 1 = ((n + k : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast, Units.smul_def, smul_eq_mul, abs_mul,
      Int.abs_negOnePow, one_mul, abs_of_nonneg (by positivity), show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]
    calc (((n + k).choose k : ℕ) : ℤ) ≤ ((2 ^ (n + k) : ℕ) : ℤ) := by exact_mod_cast Nat.choose_le_two_pow (n + k) k
      _ ≤ 2 ^ (n + 1 + k) := by push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
end ClauseBound.Rec
