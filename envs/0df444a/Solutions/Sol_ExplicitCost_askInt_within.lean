-- Prove2me | solution 1 for ExplicitCost.askInt_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:06:30.618815+00:00
-- url     : https://prove2.me/submissions/433c643c-ee21-4c6f-adfb-b1d9de6e4197

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_query_within


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
namespace ExplicitCost
theorem _root_.solution [HasSize α] {h : α → Q} {O : Q → Option Ans} {w : Q → ℕ} {a : α} {v : Ans} (hv : O (h a) = some v) : (askInt h).Within O w a (w (h a)) (max (size a) (size v) + 1) (asInt v) :=
  mapOut_within (query_within hv)
end ExplicitCost
