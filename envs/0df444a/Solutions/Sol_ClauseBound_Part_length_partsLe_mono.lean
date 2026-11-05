-- Prove2me | solution 1 for ClauseBound.Part.length_partsLe_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:58.4652+00:00
-- url     : https://prove2.me/submissions/74a8eec1-5016-4a5e-a6e3-1d2902c6c94c

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
import Definitions.Def_ClauseBound_Part_ListP
import Theorems.Thm_ClauseBound_Part_partsLe_succ

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) {k k' : ℕ} (h : k ≤ k') : (partsLe E k).length ≤ (partsLe E k').length := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hk | hk
    · rw [partsLe_succ, List.length_append]
      have := ih (by omega)
      omega
    · rw [show k = k' + 1 by omega]
end ClauseBound.Part
