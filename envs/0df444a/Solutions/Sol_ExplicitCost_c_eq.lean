-- Prove2me | solution 1 for ExplicitCost.c_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:24:44.394806+00:00
-- url     : https://prove2.me/submissions/1773f3da-f46d-4888-ba20-964e9d535b7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {a b : Fin (nParts g g tr)} (hab : a ≠ b) : (patternNet D c g tr lam y W).c a b = capG (piecesOf D c) g g tr 0 lam y a b :=
  gridN_c (piecesOf D c) [()] g g tr 0 lam y (fun w θ => W w.val (List.ofFn θ).flatten) hab
end ExplicitCost
