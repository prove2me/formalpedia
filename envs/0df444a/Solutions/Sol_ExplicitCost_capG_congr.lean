-- Prove2me | solution 1 for ExplicitCost.capG_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:21.704837+00:00
-- url     : https://prove2.me/submissions/39a1fd8e-bd41-4609-914f-8b3ff25fdfb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_lenG_congr

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {P P' : PiecesF} {h ℓ : ℕ}
namespace ExplicitCost
theorem _root_.solution (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (p d : ℕ) (tr : Bool) (y a b : ℕ) :
    capG P p d tr h ℓ y a b = capG P' p d tr h ℓ y a b := by
  unfold capG
  exact congrArg _ (Finset.sum_congr rfl fun κ _ => lenG_congr hc hpos hcap d tr y _ κ)
end ExplicitCost
