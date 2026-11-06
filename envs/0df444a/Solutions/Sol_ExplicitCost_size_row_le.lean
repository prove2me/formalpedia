-- Prove2me | solution 1 for ExplicitCost.size_row_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:46.760322+00:00
-- url     : https://prove2.me/submissions/b39888d8-cc83-4df3-ba1a-4f366f857c45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_size_nat_of_lt
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (a : Fin (nParts g g tr)) : size a.val ≤ g + 1 := by
  have h : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
  have := size_nat_of_lt (h.trans Nat.lt_two_pow_self)
  omega
end ExplicitCost
