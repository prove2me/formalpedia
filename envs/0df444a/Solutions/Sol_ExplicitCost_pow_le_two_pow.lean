-- Prove2me | solution 1 for ExplicitCost.pow_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:55.005115+00:00
-- url     : https://prove2.me/submissions/ad39e01d-443e-48d5-9288-55c9139529f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (X e : ℕ) : X ^ e ≤ 2 ^ (X * e) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le e
end ExplicitCost
