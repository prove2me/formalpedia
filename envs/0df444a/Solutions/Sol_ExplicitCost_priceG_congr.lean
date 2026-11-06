-- Prove2me | solution 1 for ExplicitCost.priceG_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:25.142455+00:00
-- url     : https://prove2.me/submissions/4daa82b6-6444-4380-8c10-431741a4a958

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Prog_digit_le


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {P P' : PiecesF} {h ℓ : ℕ}
namespace ExplicitCost
theorem _root_.solution (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (p d : ℕ) (tr : Bool) (y : ℕ) :
    priceG P p d tr h ℓ y = priceG P' p d tr h ℓ y := by
  unfold priceG
  refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
  rw [← hc]
  refine hcap tr _ ?_
  have := Prog.digit_le (P.cnt h ℓ - 1) y q
  omega
end ExplicitCost
