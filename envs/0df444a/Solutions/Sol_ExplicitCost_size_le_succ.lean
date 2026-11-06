-- Prove2me | solution 1 for ExplicitCost.size_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:59:23.983977+00:00
-- url     : https://prove2.me/submissions/270cd424-46ec-449f-aac2-d884fa94ad03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
namespace ExplicitCost
theorem _root_.solution (n : ℕ) : size n ≤ n + 1 := Nat.succ_le_succ (Nat.size_le.2 Nat.lt_two_pow_self)
end ExplicitCost
