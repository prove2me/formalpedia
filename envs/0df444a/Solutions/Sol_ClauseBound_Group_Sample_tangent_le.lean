-- Prove2me | solution 1 for ClauseBound.Group.Sample.tangent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:40.16821+00:00
-- url     : https://prove2.me/submissions/964e5614-4b1b-46ec-bb5d-27b65978471b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Group_Sample

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
variable {ι : Type} [DecidableEq ι]
open ClauseBound.Group.Sample
namespace ClauseBound.Group.Sample
theorem _root_.solution (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) (k : ℕ) : ((k : ℝ) + 1) * w * u ^ k ≤ w ^ (k + 1) + k * u ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : 0 ≤ (w ^ (k + 1) - u ^ (k + 1)) * (w - u) := by
      rcases le_total u w with h | h
      · exact mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hu h _)) (sub_nonneg.2 h)
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hw h _)) (sub_nonpos.2 h)
    have h2 := mul_le_mul_of_nonneg_right ih hu
    push_cast
    simp only [pow_succ] at key h2 ⊢
    generalize u ^ k = A at *
    generalize w ^ k = W at *
    nlinarith
end ClauseBound.Group.Sample
