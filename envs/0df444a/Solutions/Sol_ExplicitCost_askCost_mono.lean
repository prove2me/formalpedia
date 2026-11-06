-- Prove2me | solution 1 for ExplicitCost.askCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:09.331281+00:00
-- url     : https://prove2.me/submissions/9b7352ba-4061-4e03-bb99-aa52eb5b7d02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (c : ℕ) {u u' : ℕ} (h : u ≤ u') : askCost c u ≤ askCost c u' :=
  Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h)) _
end ExplicitCost
