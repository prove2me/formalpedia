-- Prove2me | solution 1 for ExplicitCost.size_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:48:00.0025+00:00
-- url     : https://prove2.me/submissions/7a1b51fa-3fa9-486a-b041-cde95b23a13c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_ExplicitCost_size_nat_of_lt


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (g : ℕ) : size (g * g) ≤ g * g + 2 := by
  have := size_nat_of_lt (Nat.lt_two_pow_self (n := g * g))
  omega
end ExplicitCost
