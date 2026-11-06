-- Prove2me | solution 1 for ExplicitCost.size_of_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:47.953854+00:00
-- url     : https://prove2.me/submissions/65843f1f-714f-4d49-b1f0-18074ed6d6a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_int
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {v : ℤ} {m : ℕ} (h : |v| < 2 ^ m) : size v ≤ m + 1 := by
  rw [size_int]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  have h1 : (v.natAbs : ℤ) < 2 ^ m := by rwa [Int.natCast_natAbs]
  exact_mod_cast h1
end ExplicitCost
