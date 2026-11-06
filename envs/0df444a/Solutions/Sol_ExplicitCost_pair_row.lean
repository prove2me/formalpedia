-- Prove2me | solution 1 for ExplicitCost.pair_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:30.719969+00:00
-- url     : https://prove2.me/submissions/e342ad62-047e-4770-b296-b80423066682

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
import Theorems.Thm_ExplicitCost_cutsOK_piecesOf
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e
import Theorems.Thm_P2M_Groundwork_Network___pull_e5947ed64801
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    (gridN (piecesOf D c) [()] g g false 0 lam y Rm).Ψ a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g false b i) = heG g g lam z' i (nodeG g false a i) then 1 else 0) *
        ∏ k : Fin g × Fin g with k.1 < k.2, pieceValue D lam (indexAt D lam (digG (piecesOf D c) g false 0 lam y (tri a.val b.val) (tri k.1 k.2))) (rectStrings g false lam ((a.val, b.val), (z, z')) k.1 k.2) := by
  have hC := cutsOK_piecesOf hS hlam [()]
  have hl : ∀ (w : List Bool), w.length = g * (g * g) * lam → ∀ (o x i : Fin g), (heG g g lam w x (nodeG g false o i)).length = lam := fun w hw o x i =>
    length_heG (tr := false) hw x.2 (nodeG_lt (p := g) false o.2 i.2)
  have hd : ∀ (w : List Bool) (x : Fin g) (w' : Fin g × Fin g), (stC g g false lam).dec w x w' = Grid.bitsOf lam (heG g g lam w x (nodeG g false w'.1 w'.2)) :=
    fun w x w' => stC_dec g g false lam w x w'
  refine (Network.Ψ_pull (gridNet (piecesOf D c) [()] g g false 0 lam y (gridR g g false lam Rm)) _ _ _ a b z z').trans ?_
  refine (rowNet_Ψ (fun ω => hC.factors false _ (digG_lt hC.cnt_pos g false y _ _)) _ _ _ hab _ _).trans ?_
  unfold rowΨ
  congr 1
  refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun e => (bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).1 ((hd z i (b, i)).symm.trans (e.trans (hd z' i (a, i)))),
    fun e => (hd z i (b, i)).trans (((bitsOf_inj (hl z hz b i i) (hl z' hz' a i i)).2 e).trans (hd z' i (a, i)).symm)⟩
end ExplicitCost
