-- Prove2me | solution 1 for ClauseBound.Part.Bits.logb_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:31.962908+00:00
-- url     : https://prove2.me/submissions/792e25f8-3535-425f-b7e2-f9a7eb29bdf4

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
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Bits

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part ClauseBound.Part.Bits
open Finset Partitions Real
namespace ClauseBound.Part.Bits
theorem _root_.solution {k h : ℕ} (hk : k ≤ 4) (hh : 1 ≤ h) : logb 2 ((k * h + 1 : ℕ) : ℝ) ≤ 3 + logb 2 h := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have h1 : ((k * h + 1 : ℕ) : ℝ) ≤ 2 ^ 3 * h := by
    have : k * h + 1 ≤ 2 ^ 3 * h := by nlinarith
    exact_mod_cast this
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_mul (by positivity) hh0.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  simp only [Nat.cast_ofNat, mul_one] at h2
  exact h2
end ClauseBound.Part.Bits
