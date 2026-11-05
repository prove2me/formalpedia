-- Prove2me | solution 1 for ClauseBound.Part.Bits.le_two_pow_of_logb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:18.711967+00:00
-- url     : https://prove2.me/submissions/ef2862d0-6459-49f2-b9d2-aa13c58589ba

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
theorem _root_.solution {r c : ℕ} (hr : 1 ≤ r) {y : ℝ} (h1 : logb 2 r ≤ y) (h2 : y ≤ c) : r ≤ 2 ^ c := by
  have h3 : (r : ℝ) ≤ (2 : ℝ) ^ (c : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hr)).1 (h1.trans h2)
  rw [Real.rpow_natCast] at h3
  exact_mod_cast h3
end ClauseBound.Part.Bits
