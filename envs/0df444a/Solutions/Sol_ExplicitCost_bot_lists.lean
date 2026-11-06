-- Prove2me | solution 1 for ExplicitCost.bot_lists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:45:45.936399+00:00
-- url     : https://prove2.me/submissions/146af089-9ffe-4575-91ca-1d10bd0e0137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (c : ℕ) (pad : U) (tr : Bool) (h j : ℕ) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) :
    (piecesOf D c).bot ((pad, tr), (h, j), (s₁, s₂, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr true (indexAt D lam j) (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ else 0 := by
  subst h1
  rfl
end ExplicitCost
