-- Prove2me | solution 1 for ExplicitCost.pieces_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:56:59.411773+00:00
-- url     : https://prove2.me/submissions/b0e3facc-6ce7-423e-8015-fafad6ccfe20

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
theorem _root_.solution {i : ℤ} (hi : i ∈ (D.fam lam).I) (tr side : Bool) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) (h2 : s₂.length = lam) (h3 : θ.length = D.cap lam tr i)
    (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) {u : List Unit} (hu : u.length = lam) :
    piecesUpTo D Lam (u, .inr (.inr (.inr (.inr ((tr, side), i, (s₁, s₂, θ)))))) = some (Sum.inl (D.fn lam tr side i (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ)) := by
  subst hu
  change (if u.length ≤ Lam then (if 1 ≤ u.length then
    (if i ∈ (D.fam u.length).I ∧ s₁.length = u.length ∧ s₂.length = u.length ∧ θ.length = D.cap u.length tr i then
      some (Sum.inl (D.fn u.length tr side i (PiecesCounted.toBits u.length s₁, PiecesCounted.toBits u.length s₂) θ)) else none) else none) else none) = _
  rw [if_pos hLam, if_pos hlam, if_pos ⟨hi, h1, h2, h3⟩]
end ExplicitCost
