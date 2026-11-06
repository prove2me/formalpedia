-- Prove2me | solution 1 for ExplicitCost.pieces_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:58.03947+00:00
-- url     : https://prove2.me/submissions/6f4ab908-23d0-446a-9b44-b407c5173747

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {i : ℤ} (hi : i ∈ (D.fam lam).I) {s : List Bool × List Bool × List Bool × List Bool} (h1 : s.1.length = lam) (h2 : s.2.1.length = lam) (h3 : s.2.2.1.length = lam) (h4 : s.2.2.2.length = lam)
    (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) {u : List Unit} (hu : u.length = lam) : piecesUpTo D Lam (u, .inr (.inr (.inr (.inl (i, s))))) = some (Sum.inl (pieceValue D lam i s)) := by
  subst hu
  change (if u.length ≤ Lam then (if 1 ≤ u.length then
    (if i ∈ (D.fam u.length).I ∧ s.1.length = u.length ∧ s.2.1.length = u.length ∧ s.2.2.1.length = u.length ∧ s.2.2.2.length = u.length then some (Sum.inl (pieceValue D u.length i s)) else none) else none) else none) = _
  rw [if_pos hLam, if_pos hlam, if_pos ⟨hi, h1, h2, h3, h4⟩]
end ExplicitCost
