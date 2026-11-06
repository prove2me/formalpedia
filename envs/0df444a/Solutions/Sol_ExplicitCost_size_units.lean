-- Prove2me | solution 1 for ExplicitCost.size_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:02:24.525735+00:00
-- url     : https://prove2.me/submissions/131f2e3a-10cf-4b3d-b8db-16cdef30385a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
import Theorems.Thm_ExplicitCost_unary_length_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_P2M_ExplicitCost_size_unary__02a080207638
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (u : List Unit) : size u = 2 * u.length + 1 := by
  have h := size_unary' u.length
  rwa [unary_length_eq] at h
end ExplicitCost
