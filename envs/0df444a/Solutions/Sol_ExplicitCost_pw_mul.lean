-- Prove2me | solution 1 for ExplicitCost.pw_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:32.709196+00:00
-- url     : https://prove2.me/submissions/bd6088a1-2024-4145-aff1-46a604b8e299

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
theorem _root_.solution {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb
end ExplicitCost
