-- Prove2me | solution 1 for ExplicitCost.length_factorChunk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:12:10.923196+00:00
-- url     : https://prove2.me/submissions/8c56089f-b4b3-4a3a-b8da-e1b52dedbf5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_ExplicitCost_nMemb_self
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_chunkAt
import Theorems.Thm_Groundwork_tri_lt
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) {j : ℕ} (hlt : j / g < j % g) (hg : 0 < g) :
    (factorChunk D c g tr lam y q j).length = D.cap lam tr (indexAt D lam (factorDigit D c g tr lam y q j)) := by
  unfold factorChunk
  refine length_chunkAt _ (r := c2 g) (tri_lt hlt (Nat.mod_lt _ hg)) ?_
  unfold capG at hθ
  rw [nMemb_self] at hθ
  rw [List.length_drop, hθ]
  omega
end ExplicitCost
