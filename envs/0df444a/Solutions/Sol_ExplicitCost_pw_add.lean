-- Prove2me | solution 1 for ExplicitCost.pw_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:11:18.781865+00:00
-- url     : https://prove2.me/submissions/6d671d00-39e2-46b2-ba17-356050e183f9

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
theorem _root_.solution {X a b i j : ℕ} (hX : 2 ≤ X) (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a + b ≤ X ^ (i + j + 1) := by
  have h1 : X ^ i ≤ X ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : X ^ j ≤ X ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * X ^ (i + j) ≤ X * X ^ (i + j) := Nat.mul_le_mul_right _ hX
  have e : X ^ (i + j + 1) = X * X ^ (i + j) := by rw [pow_succ, mul_comm]
  rw [e]
  omega
end ExplicitCost
