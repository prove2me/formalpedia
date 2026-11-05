-- Prove2me | solution 1 for ClauseBound.Part.Bits.logb_le_sqrt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:40:46.239264+00:00
-- url     : https://prove2.me/submissions/fba2d6ba-0660-4061-97bb-422d19a2dd0c

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
theorem _root_.solution {E : ℕ} (hE : 1 ≤ E) : logb 2 E ≤ 4 * √√(E : ℝ) / Real.log 2 := by
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have hy : 0 < √√(E : ℝ) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hE0)
  have h1 : (√√(E : ℝ)) ^ 4 = E := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hE0.le]
  have h2 : Real.log E = 4 * Real.log (√√(E : ℝ)) := by
    conv_lhs => rw [← h1]
    rw [Real.log_pow]
    norm_num
  have h3 := Real.log_le_sub_one_of_pos hy
  rw [Real.logb, h2]
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le
end ClauseBound.Part.Bits
