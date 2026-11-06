-- Prove2me | solution 1 for ExplicitCost.lenG_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:29:37.330483+00:00
-- url     : https://prove2.me/submissions/1e2ba4ee-dbcf-4552-b288-226a2b86b53d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_digG_congr
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {P P' : PiecesF} {h ℓ : ℕ}
namespace ExplicitCost
theorem _root_.solution (hc : P.cnt h ℓ = P'.cnt h ℓ) (hpos : 1 ≤ P.cnt h ℓ) (hcap : ∀ tr, ∀ j < P.cnt h ℓ, P.cap tr h ℓ j = P'.cap tr h ℓ j) (d : ℕ) (tr : Bool) (y q κ : ℕ) :
    lenG P d tr h ℓ y q κ = lenG P' d tr h ℓ y q κ := by
  unfold lenG
  rw [← digG_congr hc]
  exact hcap tr _ (digG_lt hpos d tr y q κ)
end ExplicitCost
