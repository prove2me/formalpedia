-- Prove2me | solution 1 for ExplicitCost.fn_bitsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:42.664276+00:00
-- url     : https://prove2.me/submissions/7e017191-21b7-4e6e-8ecf-74afdffd2964

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_ExplicitCost_toBits_bitsOf
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) {lam : ℕ} (tr side : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (if θ.length = D.cap (ClauseBound.Alg.bitsOf x).length tr (indexAt D (ClauseBound.Alg.bitsOf x).length j) then
      D.fn (ClauseBound.Alg.bitsOf x).length tr side (indexAt D (ClauseBound.Alg.bitsOf x).length j) (PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf x), PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf y)) θ else 0) =
      if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr side (indexAt D lam j) (x, y) θ else 0 := by
  have key : ∀ n, n = lam → (if θ.length = D.cap n tr (indexAt D n j) then D.fn n tr side (indexAt D n j) (PiecesCounted.toBits n (ClauseBound.Alg.bitsOf x), PiecesCounted.toBits n (ClauseBound.Alg.bitsOf y)) θ else 0) =
      if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr side (indexAt D lam j) (x, y) θ else 0 := by
    intro n hn
    subst hn
    rw [toBits_bitsOf, toBits_bitsOf]
  exact key _ (List.length_ofFn)
end ExplicitCost
