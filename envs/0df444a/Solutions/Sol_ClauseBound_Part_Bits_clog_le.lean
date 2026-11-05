-- Prove2me | solution 1 for ClauseBound.Part.Bits.clog_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:40:57.147318+00:00
-- url     : https://prove2.me/submissions/16a8938b-bb8a-42c1-8930-1cad9b0466ea

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
import Theorems.Thm_ClauseBound_Part_Bits_le_two_pow_of_logb_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part ClauseBound.Part.Bits
open Finset Partitions Real
namespace ClauseBound.Part.Bits
theorem _root_.solution {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : logb 2 r ≤ y) : (Nat.clog 2 r : ℝ) ≤ y + 1 := by
  have h0 : 0 ≤ y := (Real.logb_nonneg (by norm_num) (by exact_mod_cast hr)).trans hy
  have h1 : r ≤ 2 ^ ⌈y⌉₊ := le_two_pow_of_logb_le hr hy (Nat.le_ceil y)
  have h2 : (Nat.clog 2 r : ℝ) ≤ ⌈y⌉₊ := by exact_mod_cast Nat.clog_le_of_le_pow h1
  exact h2.trans (Nat.ceil_lt_add_one h0).le
end ClauseBound.Part.Bits
