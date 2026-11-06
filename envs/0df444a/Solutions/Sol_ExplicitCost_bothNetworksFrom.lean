-- Prove2me | solution 1 for ExplicitCost.bothNetworksFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:20:43.580551+00:00
-- url     : https://prove2.me/submissions/d70b36c3-ac7a-443e-92d8-c6b6abcd0f48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_ExplicitCost_answer_within
import Theorems.Thm_ExplicitCost_netData_eq
import Theorems.Thm_ExplicitCost_pattern_c_le
import Theorems.Thm_ExplicitCost_pattern_is


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution : BothNetworksFrom := fun hPP hLA c => ⟨2 * c + 6, fun _ _ _ hS _ _ _ _ _ _ _ _ _ _ hg hK hlam hLam hB hW hy hx =>
  ⟨pattern_is hS (by omega) hlam hB hW, fun a b _ => pattern_c_le hS hlam a b, netData_eq hLA hS hlam, fun _ _ hq => answer_within hPP hLA hS hg hK hlam hLam hB hW hy hx hq⟩⟩
end ExplicitCost
