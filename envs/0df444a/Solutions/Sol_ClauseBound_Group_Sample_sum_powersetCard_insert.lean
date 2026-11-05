-- Prove2me | solution 1 for ClauseBound.Group.Sample.sum_powersetCard_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:51.175595+00:00
-- url     : https://prove2.me/submissions/5cb4cd68-450f-40fe-8400-db6b451d40c3

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
theorem _root_.solution {a : ι} {s : Finset ι} (ha : a ∉ s) (x : ι → ℝ) (k : ℕ) :
    ∑ S ∈ powersetCard (k + 1) (insert a s), ∏ i ∈ S, x i =
      ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i + x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i := by
  have hnot : ∀ {m : ℕ} {S : Finset ι}, S ∈ powersetCard m s → a ∉ S := fun hS h => ha ((mem_powersetCard.1 hS).1 h)
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun S hS => ?_
    rw [prod_insert (hnot hS)]
  · intro S hS U hU h
    have h' := congrArg (fun V => V.erase a) h
    simpa [erase_insert (hnot hS), erase_insert (hnot hU)] using h'
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨U, _, rfl⟩ := mem_image.1 hS'
    exact hnot hS (mem_insert_self a U)
end ClauseBound.Group.Sample
