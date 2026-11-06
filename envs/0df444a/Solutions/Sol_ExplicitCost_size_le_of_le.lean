-- Prove2me | solution 1 for ExplicitCost.size_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:49:06.28513+00:00
-- url     : https://prove2.me/submissions/65b09636-bf87-453d-a40a-2dc5e175ab0c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
namespace ExplicitCost
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : size m ≤ size n := Nat.succ_le_succ (Nat.size_le_size h)
end ExplicitCost
