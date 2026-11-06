-- Prove2me | solution 1 for ExplicitCost.pw_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:19.896489+00:00
-- url     : https://prove2.me/submissions/0dbd68a1-b942-4737-b5c8-7470c888b733

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
theorem _root_.solution {X a i : ℕ} (ha : a ≤ X ^ i) (k : ℕ) : a ^ k ≤ X ^ (i * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left ha k
end ExplicitCost
