-- Prove2me | solution 1 for ExplicitCost.Xi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:49.210429+00:00
-- url     : https://prove2.me/submissions/7f9b543a-dc00-4b37-b539-8b7d595f22ed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
import Theorems.Thm_ExplicitCost_K_succ_mul


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (x₀ j u v : ℕ) : Xi (Levels.Gen.g x₀ j) u v = Levels.Gen.K x₀ (j + 1) * (u + v) := by rw [K_succ_mul, Xi, sq]
end ExplicitCost
