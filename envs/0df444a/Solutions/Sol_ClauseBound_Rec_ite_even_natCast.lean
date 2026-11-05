-- Prove2me | solution 1 for ClauseBound.Rec.ite_even_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:50.426471+00:00
-- url     : https://prove2.me/submissions/54c21d6f-0215-4b5e-bd0c-5f2f160cf290

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
theorem _root_.solution (j : ℕ) : (if Even (j : ℤ) then (1 : ℤ) else -1) = (-1) ^ j := by
  by_cases h : Even j
  · rw [if_pos (by exact_mod_cast h), h.neg_one_pow]
  · rw [if_neg (by exact_mod_cast h), (Nat.not_even_iff_odd.1 h).neg_one_pow]
end ClauseBound.Rec
