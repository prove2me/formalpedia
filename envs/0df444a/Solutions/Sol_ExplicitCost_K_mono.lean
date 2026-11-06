-- Prove2me | solution 1 for ExplicitCost.K_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:50.78926+00:00
-- url     : https://prove2.me/submissions/93f37d62-1a31-490a-a2c7-e458e3f9134c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_ExplicitCost_K_le_succ
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_succ


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ : ℕ) {k l : ℕ} (h : k ≤ l) : Levels.Gen.K x₀ k ≤ Levels.Gen.K x₀ l := monotone_nat_of_le_succ (K_le_succ x₀) h
end ExplicitCost
