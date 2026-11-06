-- Prove2me | solution 1 for ExplicitCost.top_piecesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:09:30.276856+00:00
-- url     : https://prove2.me/submissions/b6a636f8-1062-450a-9b6c-db6a28afd3e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_fn_bitsOf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (c : ℕ) {lam : ℕ} (pad : U) (tr : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (piecesOf D c).top ((pad, tr), (0, j), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr false (indexAt D lam j) (x, y) θ else 0 :=
  fn_bitsOf D tr false j x y θ
end ExplicitCost
