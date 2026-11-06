-- Prove2me | solution 1 for ExplicitCost.totalsAre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:25.523044+00:00
-- url     : https://prove2.me/submissions/95b469fc-de9c-49f8-87d7-f418ed435edb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
import Theorems.Thm_ExplicitCost_totalG_lists
import Theorems.Thm_ClauseBound_Alg_GridNet_U_gridN


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}
namespace ExplicitCost
theorem _root_.solution : TotalsAre := by
  intro ρ c x₀ D hS g lam y tr W _ hlam
  rw [totalG_lists hS hlam]
  exact U_gridN (piecesOf D c) [()] g g tr 0 lam y fun w θ => W w.val (List.ofFn θ).flatten
end ExplicitCost
