-- Prove2me | solution 1 for ExplicitCost.size_of_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:53.608349+00:00
-- url     : https://prove2.me/submissions/e8e089df-533f-468a-9a54-9648c024abe9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {n k : ℕ} (h : n ≤ 2 ^ k) : size n ≤ k + 2 :=
  Nat.succ_le_succ (Nat.size_le.2 (h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))))
end ExplicitCost
