-- Prove2me | solution 1 for ExplicitCost.rowPair_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:45:05.640063+00:00
-- url     : https://prove2.me/submissions/17a91169-3b4c-45b2-b4a6-b48eb3453589

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution : rowPair = QueryMachine.mapIn (fun x : Parent × PsiQ => (x.1, ordered x.2)) pairLoop := rfl
end ExplicitCost
