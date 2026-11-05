-- Prove2me | solution 1 for ClauseBound.Part.one_le_Rcol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:40:05.512338+00:00
-- url     : https://prove2.me/submissions/f5a72562-e72c-4798-a248-d7f91d2c6bd5

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
import Theorems.Thm_ClauseBound_Part_p_pos


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) : 1 ≤ Rcol h s := by
  have h1 := abs_le.1 hs
  have h2 : 1 ≤ pz (2 * h - s - ((0 : ℕ) : ℤ)) := by
    unfold pz
    rw [if_pos (by push_cast; omega)]
    exact p_pos _
  exact h2.trans (single_le_sum (f := fun i : ℕ => pz (2 * h - s - i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
end ClauseBound.Part
